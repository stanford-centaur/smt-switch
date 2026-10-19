/*!
 * \file exceptions.cpp
 * \brief Out-of-line members of the smt-switch exceptions.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include "exceptions.h"

const char * SmtException::what() const noexcept { return msg.c_str(); }
