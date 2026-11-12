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

/**
   Base exception for this codebase.
   All other exceptions used in the code should be derived
     classes of this.
 */

class SmtException : public std::exception
{
 public:
  /** Constructor (C strings).
   *  @param message C-style string error message.
   *                 The string contents are copied upon construction.
   *                 Hence, responsibility for deleting the char* lies
   *                 with the caller.
   */
  explicit SmtException(const char * message);

  /** Constructor (C++ STL strings).
   *  @param message The error message.
   */
  explicit SmtException(const std::string & message);

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

class IncorrectUsageException : public SmtException
{
 public:
  using SmtException::SmtException;
  // defined in the .cpp to anchor the vtable
  ~IncorrectUsageException() override;
};

class NotImplementedException : public SmtException
{
 public:
  using SmtException::SmtException;
  // defined in the .cpp to anchor the vtable
  ~NotImplementedException() override;
};

class InternalSolverException : public SmtException
{
 public:
  using SmtException::SmtException;
  // defined in the .cpp to anchor the vtable
  ~InternalSolverException() override;
};

#endif  // SMT_SWITCH_EXCEPTIONS_H
