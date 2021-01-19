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

void test_binary(string path, vector<string> args)
{
  std::cout << "testing binary: " << path << std::endl;
  std::cout << "constructing solver" << std::endl;
  SmtSolver gs = std::make_shared<GenericSolver>(path, args, 5, 5);
  std::cout << "setting an option" << std::endl;
  gs->set_opt("produce-models", "true");
}

int main() {
  // testing a non-existing binary
  string path;
  vector<string> args;
  try
  {
    path = "/non/existing/path";
    test_binary(path, args);
  }
  catch (IncorrectUsageException e)
  {
    std::cout << "caught an exception" << std::endl;
  }

// testing with cvc4 binary
#if BUILD_CVC4
  path = (STRFY(CVC4_HOME));
  path += "/build/bin/cvc4";
  args = { "--lang=smt2", "--incremental", "--dag-thresh=0" };
  test_binary(path, args);
#endif

// testing with msat binary
#if BUILD_MSAT
  path = (STRFY(MSAT_HOME));
  path += "/bin/mathsat";
  args = { "" };
  test_binary(path, args);
#endif

  // testing with cvc4 binary
#if BUILD_YICES2
  path = (STRFY(YICES2_HOME));
  path += "/build/bin/yices_smt2";
  args = { "--incremental" };
  test_binary(path, args);
#endif

  // testing with cvc4 binary
#if BUILD_BTOR
  path = (STRFY(BTOR_HOME));
  path += "/build/bin/boolector";
  args = { "--incremental" }; 
  test_binary(path, args);
#endif
}

#endif // __APPLE__
