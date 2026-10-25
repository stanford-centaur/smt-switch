/*!
 * \file exceptions.cpp
 * \brief Out-of-line members of the smt-switch exceptions.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include "exceptions.h"

SmtException::SmtException(const char * message) : msg(message) {}

SmtException::SmtException(const std::string & message) : msg(message) {}

const char * SmtException::what() const noexcept { return msg.c_str(); }

IncorrectUsageException::~IncorrectUsageException() = default;

NotImplementedException::~NotImplementedException() = default;

InternalSolverException::~InternalSolverException() = default;
