/*!
 * \file exceptions.cpp
 * \brief Out-of-line members of the smt-switch exceptions
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/exceptions.h"

namespace smt {

Exception::Exception(const char * message) : msg(message) {}

Exception::Exception(const std::string & message) : msg(message) {}

const char * Exception::what() const noexcept { return msg.c_str(); }

IncorrectUsageException::~IncorrectUsageException() = default;

ParseException::~ParseException() = default;

NotImplementedException::~NotImplementedException() = default;

SolverException::~SolverException() = default;

}  // namespace smt
