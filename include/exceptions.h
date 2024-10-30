/*********************                                                        */
/*! \file exceptions.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Custom exceptions for smt-switch.
**
**
**/

// IWYU pragma: private, include "smt.h"

#pragma once

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
  explicit SmtException(const char* message) : msg(message) {}

  /** Constructor (C++ STL strings).
   *  @param message The error message.
   */
  explicit SmtException(const std::string& message) : msg(message) {}

  /** Destructor.
   * Virtual to allow for subclassing.
   */
  virtual ~SmtException() throw() {}

  /** Returns a pointer to the (constant) error description.
   *  @return A pointer to a const char*. The underlying memory
   *          is in posession of the Exception object. Callers must
   *          not attempt to free the memory.
   */
  virtual const char* what() const throw() { return msg.c_str(); }

 protected:
  /** Error message.
   */
  std::string msg;
};

class IncorrectUsageException : public SmtException
{
 public:
  explicit IncorrectUsageException(const char * msg) : SmtException(msg){};
  explicit IncorrectUsageException(const std::string& msg) : SmtException(msg){};
};

class NotImplementedException : public SmtException
{
 public:
  explicit NotImplementedException(const char * msg) : SmtException(msg){};
  explicit NotImplementedException(const std::string& msg) : SmtException(msg){};
};

class InternalSolverException : public SmtException
{
 public:
  explicit InternalSolverException(const char * msg) : SmtException(msg){};
  explicit InternalSolverException(const std::string& msg) : SmtException(msg){};
};

