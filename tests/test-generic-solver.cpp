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

void test_bool_2(SmtSolver gs)
{
  cout << "trying to create a constant boolean term" << endl;
  Term true_term_1 = gs->make_term(true);
  Term false_term_1 = gs->make_term(false);
  cout << "got term: " << true_term_1 << endl;
  cout << "got term: " << false_term_1 << endl;

  cout << "trying to create a constant boolean term again" << endl;
  Term true_term_2 = gs->make_term(true);
  Term false_term_2 = gs->make_term(false);
  cout << "got term: " << true_term_2 << endl;
  cout << "got term: " << false_term_2 << endl;
  assert(true_term_1.get() == true_term_2.get());
  assert(false_term_1.get() == false_term_2.get());

  Term true_term = true_term_1;
  Term false_term = false_term_1;

  Result r;

  cout << "checking satisfiability with no assertions" << endl;
  gs->push(1);
  r = gs->check_sat();
  assert(r.is_sat());
  gs->pop(1);

  cout << "checking satisfiability with assertion that is true" << endl;
  gs->push(1);
  gs->assert_formula(true_term);
  r = gs->check_sat();
  assert(r.is_sat());
  gs->pop(1);

  cout << "checking satisfiability with assertion that is false" << endl;
  gs->push(1);
  gs->assert_formula(false_term);
  r = gs->check_sat();
  assert(r.is_unsat());
  gs->pop(1);

  cout << "checking satisfiability with assertions that are false and true"
       << endl;
  gs->push(1);
  gs->assert_formula(false_term);
  gs->assert_formula(true_term);
  r = gs->check_sat();
  assert(r.is_unsat());
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

void test_uf_2(SmtSolver gs)
{
  Sort s = gs->make_sort("S", 0);
  Term svar1 = gs->make_symbol("x_s1", s);
  try
  {
    Term svar2 = gs->make_symbol("x_s1", s);
  }
  catch (IncorrectUsageException e)
  {
    cout << "caught exception" << endl;
  }
}
void test_int_2(SmtSolver gs)
{
  Sort int_sort = gs->make_sort(INT);
  Term int_zero = gs->make_term(0, int_sort);
  Term int_one = gs->make_term(1, int_sort);
  cout << "making some constants" << endl;

  Term int_one_equal_zero =
      gs->make_term(Equal, TermVec({ int_one, int_zero }));

  cout << "checking some simple assertions" << endl;

  gs->push(1);
  gs->assert_formula(int_one_equal_zero);
  Result r;
  r = gs->check_sat();
  assert(r.is_unsat());
  gs->pop(1);

  gs->push(1);
  Term int_one_equal_one = gs->make_term(Equal, TermVec({ int_one, int_one }));
  gs->assert_formula(int_one_equal_one);
  r = gs->check_sat();
  assert(r.is_sat());
  gs->pop(1);
}
void test_bad_term_1(SmtSolver gs)
{
  cout << "trying to create a badly-sorted term and getting and exception"
       << endl;

  try
  {
    Sort int_sort = gs->make_sort(INT);
    Term int_zero = gs->make_term(0, int_sort);
    Term int_one = gs->make_term(1, int_sort);

    Sort bv_sort = gs->make_sort(BV, 4);
    Term bv_zero = gs->make_term(0, bv_sort);
    Term bv_one = gs->make_term(1, bv_sort);
    Term bv_one_equal_int_one =
        gs->make_term(Equal, TermVec({ bv_one, int_one }));
  }
  catch (IncorrectUsageException e)
  {
    cout << "caught expected exception " << endl;
  }
}

void test_bad_term_2(SmtSolver gs)
{
  try
  {
    Sort int_sort = gs->make_sort(INT);
    Term int_zero = gs->make_term(0, int_sort);
    Term int_one = gs->make_term(1, int_sort);

    Sort bv_sort = gs->make_sort(BV, 4);
    Term bv_zero = gs->make_term(0, bv_sort);
    Term bv_one = gs->make_term(1, bv_sort);

    Term bv_one_plus_int_one =
        gs->make_term(Equal, TermVec({ bv_one, int_one }));
  }
  catch (IncorrectUsageException e)
  {
    cout << "caught expected exception " << endl;
  }
}

void test_bv_3(SmtSolver gs)
{
  Sort bv_sort = gs->make_sort(BV, 4);
  Term bv_zero = gs->make_term(0, bv_sort);
  Term bv_one = gs->make_term(1, bv_sort);
  Term bv_minus_one_int = gs->make_term(-1, bv_sort);
  Term bv_minus_one_dec = gs->make_term("-1", bv_sort);
  Term bv_minus_one_bin = gs->make_term("1111", bv_sort, 2);
  Term bv_minus_one_hex = gs->make_term("F", bv_sort, 16);
  cout << "verify that the representations are different as expected, based on "
          "the expected textual representation."
       << endl;
  assert(bv_minus_one_int == bv_minus_one_dec);
  assert(bv_minus_one_int != bv_minus_one_bin);
  assert(bv_minus_one_int != bv_minus_one_hex);
  assert(bv_minus_one_bin != bv_minus_one_hex);
  cout << "verified " << endl;
  cout << "verify that they are semantically the same" << endl;
  gs->push(1);
  Term eq1 = gs->make_term(Equal, bv_minus_one_dec, bv_minus_one_bin);
  Term eq2 = gs->make_term(Equal, bv_minus_one_int, bv_minus_one_bin);
  Term eq3 = gs->make_term(Equal, bv_minus_one_int, bv_minus_one_dec);
  Term eq4 = gs->make_term(Equal, bv_minus_one_int, bv_minus_one_hex);
  gs->assert_formula(eq1);
  gs->assert_formula(eq2);
  gs->assert_formula(eq3);
  gs->assert_formula(eq4);
  Result r;
  r = gs->check_sat();
  assert(r.is_sat());
  cout << "verified" << endl;
  gs->pop(1);

  Term bv_one_equal_zero = gs->make_term(Equal, TermVec({ bv_one, bv_zero }));
  gs->push(1);
  gs->assert_formula(bv_one_equal_zero);
  r = gs->check_sat();
  assert(r.is_unsat());
  gs->pop(1);

  gs->push(1);
  Term bv_one_equal_one = gs->make_term(Equal, bv_one, bv_one);
  gs->assert_formula(bv_one_equal_one);
  r = gs->check_sat();
  assert(r.is_sat());
  gs->pop(1);
}
void test_bv_4(SmtSolver gs)
{
  Sort bv_sort = gs->make_sort(BV, 4);
  Term bv_zero = gs->make_term(0, bv_sort);
  Term bv_one = gs->make_term(1, bv_sort);
  Term bv_one_equal_zero = gs->make_term(Equal, TermVec({ bv_one, bv_zero }));
  gs->push(1);
  gs->assert_formula(bv_one_equal_zero);
  Result r;
  r = gs->check_sat();
  assert(r.is_unsat());
  gs->pop(1);

  gs->push(1);
  Term bv_one_equal_one = gs->make_term(Equal, bv_one, bv_one);
  gs->assert_formula(bv_one_equal_one);
  r = gs->check_sat();
  assert(r.is_sat());
  gs->pop(1);
}

void test_abv_1(SmtSolver gs)
{
  Sort bv_sort1 = gs->make_sort(BV, 4);
  Sort bv_sort2 = gs->make_sort(BV, 5);

  cout << "trying to create a sort from two sorts" << endl;
  Sort bv_to_bv = gs->make_sort(ARRAY, bv_sort1, bv_sort2);
  cout << "got sort: " << bv_to_bv << endl;
  Term arr_var = gs->make_symbol("a", bv_to_bv);
  cout << "trying to create a sort from three sorts" << endl;
  Sort bv_x_bv_to_array = gs->make_sort(FUNCTION, bv_sort1, bv_sort2, bv_to_bv);
  cout << "got sort: " << bv_x_bv_to_array << endl;
}

void test_bool(SmtSolver gs)
{
  cout << "trying to create a constant boolean term" << endl;
  Term true_term_1 = gs->make_term(true);
  Term false_term_1 = gs->make_term(false);
  cout << "got term: " << true_term_1 << endl;
  cout << "got term: " << false_term_1 << endl;

  cout << "trying to create a constant boolean term again" << endl;
  Term true_term_2 = gs->make_term(true);
  Term false_term_2 = gs->make_term(false);
  cout << "got term: " << true_term_2 << endl;
  cout << "got term: " << false_term_2 << endl;
  assert(true_term_1.get() == true_term_2.get());
  assert(false_term_1.get() == false_term_2.get());

  Term true_term = true_term_1;
  Term false_term = false_term_1;

  // TODO reset doesn't work... I don't know why.
  // gs->reset();

  Result r;

  cout << "checking satisfiability with no assertions" << endl;
  gs->push(1);
  r = gs->check_sat();
  assert(r.is_sat());
  gs->pop(1);

  cout << "checking satisfiability with assertion that is true" << endl;
  gs->push(1);
  gs->assert_formula(true_term);
  r = gs->check_sat();
  assert(r.is_sat());
  gs->pop(1);

  cout << "checking satisfiability with assertion that is false" << endl;
  gs->push(1);
  gs->assert_formula(false_term);
  r = gs->check_sat();
  assert(r.is_unsat());
  gs->pop(1);

  cout << "checking satisfiability with assertions that are false and true"
       << endl;
  gs->push(1);
  gs->assert_formula(false_term);
  gs->assert_formula(true_term);
  r = gs->check_sat();
  assert(r.is_unsat());
  gs->pop(1);
}

void test_quantifiers(SmtSolver gs)
{
  gs->push(1);
  Sort int_sort = gs->make_sort(INT);
  Term par1 = gs->make_param("par1", int_sort);
  Term par2 = gs->make_param("par2", int_sort);
  Term sum = gs->make_term(Plus, par1, par2);
  Term matrix1 = gs->make_term(Gt, par1, sum);
  Term exists1 = gs->make_term(Exists, par2, matrix1);
  Term forall1 = gs->make_term(Forall, par1, exists1);
  gs->assert_formula(forall1);
  Result result = gs->check_sat();
  assert(result.is_sat());

  Term matrix2 = gs->make_term(Gt, par1, par2);
  Term forall2 = gs->make_term(Forall, par1, matrix2);
  Term exists2 = gs->make_term(Exists, par2, forall2);
  gs->assert_formula(exists2);
  result = gs->check_sat();
  assert(result.is_unsat());
  gs->pop(1);
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
  test_uf_1(gs);

  new_msat(gs);
  test_bool_1(gs);

  new_msat(gs);
  test_bool_2(gs);

  new_msat(gs);
  test_int_1(gs);

  new_msat(gs);
  test_bv_1(gs);

  new_msat(gs);
  test_bv_2(gs);

  new_msat(gs);
  test_uf_2(gs);

  new_msat(gs);
  test_int_2(gs);

  new_msat(gs);
  test_bad_term_1(gs);

  new_msat(gs);
  test_bad_term_2(gs);

  new_msat(gs);
  test_bv_3(gs);

  new_msat(gs);
  test_bv_4(gs);

  new_msat(gs);
  test_abv_1(gs);

  new_msat(gs);
  test_bool(gs);
}

void test_yices2()
{
  cout << "testing yices2" << endl;
  SmtSolver gs;

  new_yices2(gs);
  test_bad_cmd(gs);

  new_yices2(gs);
  test_uf_1(gs);

  new_yices2(gs);
  test_bool_1(gs);

  new_yices2(gs);
  test_bool_2(gs);

  new_yices2(gs);
  test_int_1(gs);

  new_yices2(gs);
  test_bv_1(gs);

  new_yices2(gs);
  test_bv_2(gs);

  new_yices2(gs);
  test_uf_2(gs);

  new_yices2(gs);
  test_int_2(gs);

  new_yices2(gs);
  test_bad_term_1(gs);

  new_yices2(gs);
  test_bad_term_2(gs);

  new_yices2(gs);
  test_bv_3(gs);

  new_yices2(gs);
  test_bv_4(gs);

  new_yices2(gs);
  test_abv_1(gs);

  new_yices2(gs);
  test_bool(gs);
}

void test_cvc4()
{
  cout << "testing cvc4" << endl;
  SmtSolver gs;

  new_cvc4(gs);
  test_bad_cmd(gs);

  new_cvc4(gs);
  test_uf_1(gs);

  new_cvc4(gs);
  test_bool_1(gs);

  new_cvc4(gs);
  test_bool_2(gs);

  new_cvc4(gs);
  test_int_1(gs);

  new_cvc4(gs);
  test_bv_1(gs);

  new_cvc4(gs);
  test_bv_2(gs);

  new_cvc4(gs);
  test_uf_2(gs);

  new_cvc4(gs);
  test_int_2(gs);

  new_cvc4(gs);
  test_bad_term_1(gs);

  new_cvc4(gs);
  test_bad_term_2(gs);

  new_cvc4(gs);
  test_bv_3(gs);

  new_cvc4(gs);
  test_bv_4(gs);

  new_cvc4(gs);
  test_abv_1(gs);

  new_cvc4(gs);
  test_bool(gs);

  new_cvc4(gs);
  test_quantifiers(gs);
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
  test_bool_2(gs);

  new_btor(gs);
  test_bv_1(gs);

  new_btor(gs);
  test_bv_2(gs);

  new_btor(gs);
  test_bv_3(gs);

  new_btor(gs);
  test_bv_4(gs);

  new_btor(gs);
  test_abv_1(gs);

  new_btor(gs);
  test_bool(gs);
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
