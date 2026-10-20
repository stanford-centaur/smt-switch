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
};

class NotImplementedException : public SmtException
{
 public:
  using SmtException::SmtException;
};

class InternalSolverException : public SmtException
{
 public:
  using SmtException::SmtException;
};
