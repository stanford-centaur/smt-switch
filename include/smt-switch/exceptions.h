/*!
 * \file exceptions.h
 * \brief Custom exceptions for smt-switch
 * \author Makai Mann
 * \author Clark Barrett
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_EXCEPTIONS_H
#define SMT_SWITCH_EXCEPTIONS_H

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#include <exception>
#include <string>

namespace smt {

/** Base of every exception smt-switch throws. Catch it to handle any of
 *  them; the subclasses say what went wrong.
 */
class Exception : public std::exception
{
 public:
  /** Constructor (C strings).
   *  @param message C-style string error message.
   *                 The string contents are copied upon construction.
   *                 Hence, responsibility for deleting the char* lies
   *                 with the caller.
   */
  explicit Exception(const char * message);

  /** Constructor (C++ STL strings).
   *  @param message The error message.
   */
  explicit Exception(const std::string & message);

  /** Returns a pointer to the (constant) error description.
   *  @return A pointer to a const char*. The underlying memory
   *          is in possession of the Exception object. Callers must
   *          not attempt to free the memory.
   */
  const char * what() const noexcept override;

 protected:
  /** Error message.
   */
  std::string msg;
};

/** Thrown when the caller asks for something SMT-LIB, or the solver's
 *  documented contract for an extension, does not allow: a value of the
 *  wrong sort, a name that is not a logic, or a call the solver's current
 *  state rules out.
 */
class IncorrectUsageException : public Exception
{
 public:
  using Exception::Exception;
  // defined in the .cpp to anchor the vtable
  ~IncorrectUsageException() override;
};

/** Thrown when SmtLibReader cannot parse its input: a syntax error, a
 *  symbol, sort or character it does not know, or something it or the
 *  solver refuses, such as a redeclaration. The message starts with where,
 *  as file:line.column.
 */
class ParseException : public Exception
{
 public:
  using Exception::Exception;
  // defined in the .cpp to anchor the vtable
  ~ParseException() override;
};

/** Thrown for a request that is allowed but that the solver, or its
 *  smt-switch backend, cannot carry out: an option it does not know, a
 *  logic or theory it lacks, or turning off an option it always keeps on.
 */
class NotImplementedException : public Exception
{
 public:
  using Exception::Exception;
  // defined in the .cpp to anchor the vtable
  ~NotImplementedException() override;
};

/** Thrown when the solver itself fails, for instance by hitting an
 *  internal limit or assertion.
 */
class SolverException : public Exception
{
 public:
  using Exception::Exception;
  // defined in the .cpp to anchor the vtable
  ~SolverException() override;
};

}  // namespace smt

#endif  // SMT_SWITCH_EXCEPTIONS_H
