/*********************                                                        */
/*! \file test-utils.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Convenience functions for testing.
**
**
**/
#pragma once

#include "smt.h"

// macros for getting string value of another macro
// i.e. STRFY(FOO) := "FOO"
#define STRHELPER(A) #A
#define STRFY(A) STRHELPER(A)

namespace smt_tests {

smt::UnorderedTermSet get_free_symbols(smt::Term & t);
}
