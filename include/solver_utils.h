/*********************                                                        */
/*! \file solver_utils.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Utility functions for solver implementations. Meant for internal
**        use only, not from the API.
**
**/
#pragma once

#include <cstddef>
#include <cstdint>
#include <limits>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "exceptions.h"
#include "ops.h"
#include "smt_defs.h"
#include "sort.h"
#include "term.h"

namespace smt {

/** Apply an operator to more than two arguments as SMT-LIB defines it in
 *  terms of applications to two, for a solver that takes no more: fold a
 *  :left-assoc or :right-assoc operator from that side, and conjoin the
 *  applications to each argument and the next for a :chainable one, or to
 *  each pair of arguments for a :pairwise one.
 *  @param solver the solver to build the terms with
 *  @param op the operator
 *  @param terms the arguments, at least two
 *  @return the application
 *  @throws IncorrectUsageException if SMT-LIB defines no such application
 */
Term make_nary_term(const AbsSmtSolver * solver,
                    const Op & op,
                    const TermVec & terms);

/** Check the arguments of a quantifier: one or more params, then the body.
 *  A solver whose API would bind a term of another kind, crash on one, or
 *  return the body unchanged when there are none checks with this first.
 *  @param op the quantifier, Forall or Exists, used in the error message
 *  @param terms the arguments
 *  @throws IncorrectUsageException if there is no param, or a term other
 *  than the body is not a param
 */
void check_quantifier_binders(const Op & op, const TermVec & terms);

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
namespace detail {

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

/** The value of c as a digit of a numeral in a base up to 36: 0 to 9,
 *  then a to z in either case
 *  @param c the character
 *  @return its value, or 36 if c is no such digit
 */
unsigned numeral_digit(char c);

/** The two's complement of the bit-vector value val, a numeral in base
 *  `base` with an optional leading minus, as AbsSmtSolver::make_term
 *  accepts it
 *  @param val the value
 *  @param base from 2 to 36
 *  @param width the width of the bit-vector
 *  @return its bits in 32-bit words, least significant first, as many as
 *  width bits take; bits of the last word above width are zero
 *  @throws IncorrectUsageException for another base, a val that is not
 *  such a numeral, or a value outside the smallest signed and the largest
 *  unsigned value of width bits
 */
std::vector<std::uint32_t> bv_value_to_words(const std::string & val,
                                             std::uint64_t base,
                                             std::uint64_t width);

/** bv_value_to_words as one number, for a width of at most 64 */
std::uint64_t bv_value_to_uint64(const std::string & val,
                                 std::uint64_t base,
                                 std::uint64_t width);

}  // namespace detail

/** Whether val is a number a value of sort kind sk, INT or REAL, can be
 *  made from, with an optional leading minus: a decimal numeral, or for a
 *  REAL also a decimal or a fraction of numerals. The slash of a fraction
 *  may have spaces around it, as TermTranslator writes one.
 *  Solvers read some other strings, such as "" or "1.2.3", without an
 *  error but not as the number meant, so check before handing one over.
 *  @param sk the sort kind of the value, INT or REAL
 *  @param val the string to check
 *  @return true iff val is such a number
 */
bool is_arith_number(SortKind sk, const std::string & val);

/** The number val names in base `base`, written for is_arith_number: val
 *  itself in base 10, and otherwise the same number in decimal, a REAL
 *  with a point as a fraction. In another base, val is a numeral, or for a
 *  REAL a decimal or fraction of numerals, of digits in that base (0 to 9,
 *  then a to z in either case), with an optional leading minus.
 *  @param sk the sort kind of the value, INT or REAL
 *  @param val the number in base `base`
 *  @param base from 2 to 36
 *  @return the number in base 10
 *  @throws IncorrectUsageException for another base, or a val in a base
 *  other than 10 that is not such a number
 */
std::string arith_value_to_decimal(SortKind sk,
                                   const std::string & val,
                                   std::uint64_t base);

/** The index-value map that a chain of stores over a constant base stands
 *  for, given the index and value each store along it writes. A backend
 *  reads its model by peeling the outer store first, so that is the order
 *  these come in, and since an outer store shadows an inner one at the same
 *  index, an index written more than once keeps the outermost assignment.
 *  @param stores the index and value each store writes, outermost first
 *  @return the map from index to value
 */
UnorderedTermMap store_chain_values(
    const std::vector<std::pair<Term, Term>> & stores);

}  // namespace smt
