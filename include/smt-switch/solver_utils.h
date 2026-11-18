/*!
 * \file solver_utils.h
 * \brief Utility functions for solver implementations
 * \author Makai Mann
 * \author Áron Ricardo Perez-Lopez
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_SOLVER_UTILS_H
#define SMT_SWITCH_SOLVER_UTILS_H

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <memory>
#include <string>
#include <string_view>
#include <type_traits>

#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"

namespace smt::backend {

/** Narrow an operator index to the 32 bits that most solver APIs take.
 *  Op stores indices as 64-bit, so without this the conversion is silent and
 *  a too-large index reaches the solver as an unrelated value.
 *  @param op the operator the index belongs to, used in the error message
 *  @param idx the index to narrow
 *  @return idx as a 32-bit value
 *  @throws IncorrectUsageException if idx does not fit
 */
std::uint32_t narrow_index(const Op & op, std::uint64_t idx);

/** Narrow a bit-vector width to the 32 bits that solver APIs take
 *  @param width the width to narrow
 *  @return width as a 32-bit value
 *  @throws IncorrectUsageException if width does not fit
 */
std::uint32_t narrow_width(std::uint64_t width);

/** Narrow a number of levels to push or pop to the 32 bits that solver APIs
 *  take
 *  @param levels the number of levels to narrow
 *  @return levels as a 32-bit value
 *  @throws IncorrectUsageException if levels does not fit
 */
std::uint32_t narrow_levels(std::uint64_t levels);

/** Narrow a number of arguments, such as of an application or a function
 *  sort, to the 32 bits that solver APIs take
 *  @param num_args the number of arguments to narrow
 *  @return num_args as a 32-bit value
 *  @throws IncorrectUsageException if num_args does not fit
 */
std::uint32_t narrow_num_args(std::size_t num_args);

// The general forms of the checks above, for the kinds no wrapper covers
/** Whether an integer of any type has the same value as a T
 *  @param value the value to check
 *  @return true iff value is in T's range
 */
template <typename T, typename U>
constexpr bool fits_in(U value)
{
  static_assert(std::is_integral_v<T> && std::is_integral_v<U>,
                "only integers are compared");
  using To = std::numeric_limits<T>;
  using From = std::numeric_limits<U>;
  // Each comparison is left out where every U fits, so none is tautological.
  if constexpr (std::is_unsigned_v<U>)
  {
    // T's maximum is positive, so it compares with value as unsigned.
    constexpr auto max = static_cast<std::make_unsigned_t<T>>(To::max());
    if constexpr (From::max() > max)
    {
      return value <= max;
    }
    else
    {
      return true;
    }
  }
  else if constexpr (std::is_signed_v<T>)
  {
    if constexpr (From::min() < To::min() || From::max() > To::max())
    {
      return value >= To::min() && value <= To::max();
    }
    else
    {
      return true;
    }
  }
  else if constexpr (static_cast<std::make_unsigned_t<U>>(From::max())
                     > To::max())
  {
    return value >= 0
           && static_cast<std::make_unsigned_t<U>>(value) <= To::max();
  }
  else
  {
    return value >= 0;
  }
}

/** Narrow an integer to the type a solver API takes it as, such as the
 *  number of arguments of an application or a bit-vector width.
 *  Without this the conversion is silent and a value outside T's range
 *  reaches the solver as an unrelated one.
 *  @param value the value to narrow, of any integer type
 *  @param what what value is, as "a bit-vector width", used in the error
 *         message
 *  @return value as a T
 *  @throws IncorrectUsageException if value does not fit
 */
template <typename T, typename U>
T narrow(U value, const char * what)
{
  if (!fits_in<T>(value))
  {
    using To = std::numeric_limits<T>;
    throw IncorrectUsageException("This solver takes " + std::string(what)
                                  + " from " + std::to_string(To::min())
                                  + " to " + std::to_string(To::max())
                                  + ", not " + std::to_string(value));
  }
  return static_cast<T>(value);
}

/** The value of a Boolean option that smt-switch interprets itself, such as
 *  produce-models or incremental
 *  @param option the option, used in the error message
 *  @param value the value given for it
 *  @return whether value is true
 *  @throws IncorrectUsageException for a value other than true or false
 */
bool parse_bool_opt(const std::string & option, const std::string & value);

/** The value of the time-limit option
 *  @param value the value given for it, in seconds
 *  @return the limit
 *  @throws IncorrectUsageException for a value that is not a nonnegative
 *  number
 */
std::chrono::duration<double> parse_time_limit(const std::string & value);

/** Opens a pipe whose ends any later exec closes, so that no program
 *  another child runs holds them
 *  @param fds receives the read end, then the write end, or -1 for both
 *  if it fails
 *  @return 0, or the errno of the call that failed
 */
int make_cloexec_pipe(int (&fds)[2]);

/** Throws the IncorrectUsageException that pointer_cast raises for
 *  a pointer made by another solver
 *  @param h the foreign pointer, named in the message
 */
[[noreturn]] void throw_foreign_pointer(const Term & h);
[[noreturn]] void throw_foreign_pointer(const Sort & h);
[[noreturn]] void throw_foreign_pointer(const DatatypeDecl & h);
[[noreturn]] void throw_foreign_pointer(const DatatypeConstructorDecl & h);
[[noreturn]] void throw_foreign_pointer(const Datatype & h);

/** Mixes a part's hash into one being built up, as Boost's hash_combine
 *  does: 0x9e3779b9 is 2^32 / golden ratio, whose irregular bits spread
 *  the value, and the shifts mix in the hash so far, so the order of the
 *  parts matters and equal parts don't cancel out
 *  @param h the hash so far, updated in place
 *  @param v the next part, hashed with std::hash
 */
template <class T>
void hash_combine(std::size_t & h, const T & v)
{
  h ^= std::hash<T>{}(v) + 0x9e3779b9 + (h << 6) + (h >> 2);
}

/** Casts a handle to the class the solver made it as
 *  @param h the handle a caller passed to the solver
 *  @return h as a T, or null for a null handle
 *  @throws IncorrectUsageException if h was made by another solver, or by a
 *          wrapper around this one
 */
template <class T, class Base>
std::shared_ptr<T> pointer_cast(const std::shared_ptr<Base> & h)
{
  std::shared_ptr<T> cast = std::dynamic_pointer_cast<T>(h);
  if (h && !cast)
  {
    throw_foreign_pointer(h);
  }
  return cast;
}

/** The start of every name internal_name makes. A solver that makes such
 *  names refuses a user name with this start, so the two never meet.
 */
inline constexpr std::string_view INTERNAL_NAME_PREFIX = "smt_switch_internal_";

/** A name smt-switch makes up for its own use, such as
 *  `smt_switch_internal_assump_3`
 *  @param kind what the name is for, which keeps names of different kinds
 *  apart
 *  @param index which name of that kind it is
 *  @return INTERNAL_NAME_PREFIX, then `kind`, an underscore and `index`
 */
std::string internal_name(const std::string & kind, std::uint64_t index);

/** Whether a name starts with INTERNAL_NAME_PREFIX
 *  @param name the name to check
 *  @return true if internal_name could have made it
 */
bool is_internal_name(std::string_view name);

}  // namespace smt::backend

#endif  // SMT_SWITCH_SOLVER_UTILS_H
