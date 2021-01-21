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

void test_bad_cmd(SmtSolver gs)
{
  cout << "trying a bad command:" << endl;
  try
  {
    gs->set_opt("iiiaaaaiiiiaaaa", "aaa");
  }
  catch (IncorrectUsageException e)
  {
    cout << "caught the exception" << endl;
  }
}

void test_uf_1(SmtSolver gs)
{
  Sort s = gs->make_sort("S", 0);
  cout << "created a sort! " << s << endl;
  cout << "trying to create it again" << endl;
  try
  {
    Sort s1 = gs->make_sort("S", 1);
  }
  catch (IncorrectUsageException e)
  {
    cout << "caught the exception" << endl;
  }
}

void test_bool_1(SmtSolver gs)
{
  Sort bool_sort = gs->make_sort(BOOL);
  Term term_1 = gs->make_symbol("term_1", bool_sort);
  Result r;
  cout << "checking satisfiability with no assertions" << endl;
  gs->push(1);
  r = gs->check_sat();
  assert(r.is_sat());
  gs->pop(1);

  cout << "checking satisfiability with assertion " << std::endl;
  gs->push(1);
  gs->assert_formula(term_1);
  r = gs->check_sat();
  assert(r.is_sat());
  gs->pop(1);
}

void test_int_1(SmtSolver gs)
{
  Sort int_sort = gs->make_sort(INT);
  cout << "created sort of sort kind " << to_string(INT)
       << ". The sort is: " << int_sort << endl;

  Sort int_sort2 = gs->make_sort(INT);
  assert(int_sort == int_sort2);

  cout << "trying to create a sort in a wrong way" << endl;
  try
  {
    Sort err_sort = gs->make_sort(ARRAY);
  }
  catch (IncorrectUsageException e)
  {
    cout << "caught the exception" << endl;
  }
}

void test_bv_1(SmtSolver gs)
{
  Sort bv_sort = gs->make_sort(BV, 4);
  cout << "created bit-vector sort: " << bv_sort << endl;

  cout << "checking for equalities" << endl;
  Sort bv_sort1 = gs->make_sort(BV, 4);
  assert(bv_sort == bv_sort1);
  Sort bv_sort2 = gs->make_sort(BV, 5);
  assert(bv_sort != bv_sort2);

  cout << "trying to create a sort in a wrong way" << endl;
  try
  {
    Sort err_sort = gs->make_sort(INT, bv_sort);
  }
  catch (IncorrectUsageException e)
  {
    cout << "caught the exception" << endl;
  }
}

void test_bv_2(SmtSolver gs)
{
  cout << "trying to create a sort in a wrong way" << endl;
  try
  {
    Sort err_sort = gs->make_sort(INT, 4);
  }
  catch (IncorrectUsageException e)
  {
    cout << "caught the exception" << endl;
  }
}

void init_solver(SmtSolver gs)
{
  gs->set_opt("produce-models", "true");
  gs->set_opt("produce-unsat-assumptions", "true");
  gs->set_logic("ALL");
}

void new_btor(SmtSolver & gs)
{
  gs.reset();
  string path = (STRFY(BTOR_HOME));
  path += "/build/bin/boolector";
  vector<string> args = { "--incremental" };
  gs = std::make_shared<GenericSolver>(path, args, 5, 5);
  init_solver(gs);
}

void new_msat(SmtSolver & gs)
{
  gs.reset();
  string path = (STRFY(MSAT_HOME));
  path += "/bin/mathsat";
  vector<string> args = { "" };
  gs = std::make_shared<GenericSolver>(path, args, 5, 5);
  init_solver(gs);
}

void new_yices2(SmtSolver & gs)
{
  gs.reset();
  string path = (STRFY(YICES2_HOME));
  path += "/build/bin/yices_smt2";
  vector<string> args = { "--incremental" };
  gs = std::make_shared<GenericSolver>(path, args, 5, 5);
  init_solver(gs);
}

void new_cvc4(SmtSolver & gs)
{
  gs.reset();
  string path = (STRFY(CVC4_HOME));
  path += "/build/bin/cvc4";
  vector<string> args = { "--lang=smt2", "--incremental", "--dag-thresh=0" };
  gs = std::make_shared<GenericSolver>(path, args, 5, 5);
  init_solver(gs);
}

void test_msat()
{
  cout << "testing msat" << endl;
  SmtSolver gs;

  new_msat(gs);
  test_bad_cmd(gs);

  new_msat(gs);
  test_bool_1(gs);

  new_msat(gs);
  test_uf_1(gs);

  new_msat(gs);
  test_int_1(gs);

  new_msat(gs);
  test_bv_1(gs);

  new_msat(gs);
  test_bv_2(gs);
}

void test_yices2()
{
  cout << "testing yices2" << endl;
  SmtSolver gs;

  new_yices2(gs);
  test_bad_cmd(gs);

  new_yices2(gs);
  test_bool_1(gs);

  new_yices2(gs);
  test_uf_1(gs);

  new_yices2(gs);
  test_int_1(gs);

  new_yices2(gs);
  test_bv_1(gs);

  new_yices2(gs);
  test_bv_2(gs);
}

void test_cvc4()
{
  cout << "testing cvc4" << endl;
  SmtSolver gs;

  new_cvc4(gs);
  test_bad_cmd(gs);

  new_cvc4(gs);
  test_bool_1(gs);

  new_cvc4(gs);
  test_uf_1(gs);

  new_cvc4(gs);
  test_int_1(gs);

  new_cvc4(gs);
  test_bv_1(gs);

  new_cvc4(gs);
  test_bv_2(gs);
}

void test_btor()
{
  cout << "testing btor" << endl;
  SmtSolver gs;

  new_btor(gs);
  test_bad_cmd(gs);

  new_btor(gs);
  test_bool_1(gs);

  new_btor(gs);
  test_bv_1(gs);

  new_btor(gs);
  test_bv_2(gs);
}

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
  std::cout << "testing cvc4" << std::endl;
  test_cvc4();
#endif

// testing with msat binary
#if BUILD_MSAT
  std::cout << "testing msat" << std::endl;
  test_msat();
#endif

  // testing with yices2binary
#if BUILD_YICES2
  std::cout << "testing yices2" << std::endl;
  test_yices2();
#endif

  // testing with btorbinary
#if BUILD_BTOR
  std::cout << "testing btor" << std::endl;
  test_btor();
#endif
}

#endif  // __APPLE__
