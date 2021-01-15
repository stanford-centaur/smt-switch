/*********************                                                        */
/*! \file test-generic-solver.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
**
**
**/

// generic solvers are not supported on macos
#ifndef __APPLE__

#include <array>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include "assert.h"

// note: this file depends on the CMake build infrastructure
// specifically defined macros
// it cannot be compiled outside of the build
#include "cvc4_factory.h"
#include "generic_solver.h"
#include "generic_sort.h"
#include "generic_term.h"
#include "gtest/gtest.h"
#include "smt.h"
#include "test-utils.h"

using namespace smt;
using namespace std;

int main() {

#if BUILD_CVC4
  cout << "testing with CVC4 binary" << endl;
  GenericSolver s(STRFY(CVC4_HOME), std::vector<string>{"--lang=smt2", "--incremental", "--dag-thresh=0"}, 5, 5);
#endif
}

#endif // __APPLE__
