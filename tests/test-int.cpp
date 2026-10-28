/*********************                                                        */
/*! \file test-int.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for theory of integers.
**
**
**/

#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "exceptions.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IntTests);
class IntTests : public ::testing::Test,
                 public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    intsort = s->make_sort(INT);
  }
  SmtSolver s;
  Sort intsort;
};

TEST_P(IntTests, IntDiv)
{
  Term five = s->make_term(5, intsort);
  Term two = s->make_term(2, intsort);
  Term res = s->make_symbol("res", intsort);
  Term div = s->make_term(IntDiv, five, two);
  s->assert_formula(s->make_term(Equal, res, div));
  s->check_sat();
  Term resval = s->get_value(res);
  ASSERT_EQ(resval, two);
}

TEST_P(IntTests, BvToNatIsInt)
{
  Sort bvsort = s->make_sort(BV, 8);
  Term bvx = s->make_symbol("bvx", bvsort);
  Term natx;
  try
  {
    natx = s->make_term(BV_To_Nat, bvx);
  }
  catch (const SmtException & e)
  {
    GTEST_SKIP() << e.what();
  }
  EXPECT_EQ(natx->get_sort(), intsort);
}

TEST_P(IntTests, Bv2Int)
{
  Sort bvsort = s->make_sort(BV, 8);
  Term bvx = s->make_symbol("bvx", bvsort);

  Term intx;
  try
  {
    intx = s->make_term(UBV_To_Int, bvx);
  }
  catch (SmtException & e)
  {
    std::cout << "Got exception when trying to apply UBV_To_Int: " << e.what()
              << std::endl;
    // it's fine if this op is not supported, just end the test
    return;
  }

  ASSERT_TRUE(intx);
  EXPECT_EQ(intx->get_sort(), intsort);
  EXPECT_EQ(intx->get_op(), UBV_To_Int);

  Term inty = s->make_symbol("inty", intsort);
  Term bvy = s->make_term(Op(Int_To_BV, 8), inty);
  EXPECT_EQ(bvy->get_sort(), bvsort);
  EXPECT_EQ(bvy->get_op(), Op(Int_To_BV, 8));

  Term intz;
  try
  {
    intz = s->make_term(SBV_To_Int, bvx);
  }
  catch (SmtException & e)
  {
    std::cout << "Got exception when trying to apply SBV_To_Int: " << e.what()
              << std::endl;
    // it's fine if this op is not supported, just end the test
    return;
  }

  ASSERT_TRUE(intz);
  EXPECT_EQ(intz->get_sort(), intsort);
  if (intz->get_op() != SBV_To_Int)
  {
    // Some solvers (e.g., Z3) have different implementations that predate
    // SMT-LIB support for this operation.
    std::cout << "Got " << intz->get_op().to_string()
              << " when checking SBV_To_Int" << std::endl;
  }
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverIntTests,
    IntTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_INT })));

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IntArithmeticTests);
class IntArithmeticTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    intsort = s->make_sort(INT);
  }
  SmtSolver s;
  Sort intsort;
};

TEST_P(IntArithmeticTests, NonlinearConstraints)
{
  // whether a solver handles nonlinear arithmetic can depend on how it was
  // built: Yices2 needs MCSAT for it
  try
  {
    s->set_logic("QF_NIA");
  }
  catch (const IncorrectUsageException & e)
  {
    GTEST_SKIP() << e.what();
  }
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  s->assert_formula(s->make_term(Ge, x, y));
  s->assert_formula(s->make_term(Le, z, s->make_term(Plus, x, y)));
  s->assert_formula(
      s->make_term(Lt, s->make_term(Negate, z), s->make_term(Minus, x, y)));
  s->assert_formula(
      s->make_term(Gt, s->make_term(Minus, x, y), s->make_term(Mult, x, y)));

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  // the model is not unique, so check that it satisfies each constraint
  int64_t xv = s->get_value(x)->to_signed_int();
  int64_t yv = s->get_value(y)->to_signed_int();
  int64_t zv = s->get_value(z)->to_signed_int();
  EXPECT_GE(xv, yv);
  EXPECT_LE(zv, xv + yv);
  EXPECT_LT(-zv, xv - yv);
  EXPECT_GT(xv - yv, xv * yv);
}

TEST_P(IntArithmeticTests, PowerOfSymbol)
{
  // as in NonlinearConstraints
  try
  {
    s->set_logic("QF_NIA");
  }
  catch (const IncorrectUsageException & e)
  {
    GTEST_SKIP() << e.what();
  }
  Term u = s->make_symbol("u", intsort);
  s->assert_formula(s->make_term(Gt, u, s->make_term(0, intsort)));
  s->assert_formula(s->make_term(Equal,
                                 s->make_term(Pow, u, s->make_term(4, intsort)),
                                 s->make_term(81, intsort)));

  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_EQ(s->get_value(u)->to_signed_int(), 3);
}

INSTANTIATE_TEST_SUITE_P(
    ,
    IntArithmeticTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_INT })),
    ConfigName());

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IntBVArithmeticTests);
class IntBVArithmeticTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    s->set_opt("incremental", "true");
    intsort = s->make_sort(INT);
    bvsort = s->make_sort(BV, 8);
  }

  /** Expects constraint to be satisfiable */
  void expect_sat(const Term & constraint)
  {
    s->push();
    s->assert_formula(constraint);
    EXPECT_TRUE(s->check_sat().is_sat()) << constraint;
    s->pop();
  }

  SmtSolver s;
  Sort intsort, bvsort;
};

TEST_P(IntBVArithmeticTests, PolynomialConstraints)
{
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term z = s->make_symbol("z", bvsort);
  Term a = s->make_symbol("a", intsort);
  Term b = s->make_symbol("b", intsort);
  Term c = s->make_symbol("c", intsort);
  Term d = s->make_symbol("d", intsort);
  Term three = s->make_term(3, intsort);
  Term four = s->make_term(4, intsort);
  Term a_lt_b = s->make_term(Lt, a, b);
  Term bv_sum = s->make_term(BVAdd, x, s->make_term(BVMul, y, z));
  EXPECT_EQ(bv_sum->get_sort(), bvsort);

  // every constraint is satisfiable: the bit-vectors and b can be zero with
  // a = -1 or 0, or b = 12 and d = 88
  expect_sat(s->make_term(
      And, s->make_term(Equal, c, s->make_term(Pow, b, four)), a_lt_b));
  expect_sat(s->make_term(
      And, s->make_term(Equal, z, s->make_term(BVMul, x, y)), a_lt_b));
  expect_sat(s->make_term(
      And, s->make_term(Equal, z, s->make_term(BVAdd, x, y)), a_lt_b));
  expect_sat(s->make_term(And, s->make_term(Equal, z, bv_sum), a_lt_b));
  expect_sat(s->make_term(And,
                          s->make_term(Equal, z, bv_sum),
                          s->make_term(Equal, a, s->make_term(Pow, b, four))));
  expect_sat(s->make_term(And,
                          s->make_term(Equal, z, bv_sum),
                          s->make_term(Equal, a, s->make_term(Pow, b, three))));
  Term twelve = s->make_term(12, intsort);
  Term hundred = s->make_term(100, intsort);
  expect_sat(
      s->make_term(And,
                   s->make_term(Equal, hundred, s->make_term(Plus, b, d)),
                   s->make_term(Ge, b, twelve)));

  // and this one forces b = 45
  s->assert_formula(s->make_term(
      Equal, hundred, s->make_term(Plus, b, s->make_term(55, intsort))));
  s->assert_formula(s->make_term(Ge, b, twelve));
  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_EQ(s->get_value(b)->to_signed_int(), 45);
}

INSTANTIATE_TEST_SUITE_P(
    ,
    IntBVArithmeticTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_INT, THEORY_BV })),
    ConfigName());

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IntRealArithmeticTests);
class IntRealArithmeticTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    intsort = s->make_sort(INT);
    realsort = s->make_sort(REAL);
  }
  SmtSolver s;
  Sort intsort, realsort;
};

TEST_P(IntRealArithmeticTests, Sorts)
{
  // every solver makes arithmetic over an Int and a Real a Real, so the
  // logging and generic solvers must report one too
  Term i = s->make_symbol("i", intsort);
  Term x = s->make_symbol("x", realsort);
  for (PrimOp po : { Plus, Minus, Mult })
  {
    EXPECT_EQ(s->make_term(po, i, x)->get_sort(), realsort);
    EXPECT_EQ(s->make_term(po, x, i)->get_sort(), realsort);
    EXPECT_EQ(s->make_term(po, i, i)->get_sort(), intsort);
  }
}

TEST_P(IntRealArithmeticTests, Div)
{
  // unlike IntDiv, Div (/) divides Ints as Reals, and an Int by a Real.
  // SMT-LIB declares / only over Reals, but cvc5, MathSAT and Yices2 take
  // Ints as well; to be strict instead, every backend would have to throw an
  // IncorrectUsageException here
  Term two = s->make_term(2, realsort);
  Term quotient =
      s->make_term(Div, s->make_term(7, intsort), s->make_term(2, intsort));
  EXPECT_EQ(quotient->get_sort(), realsort);
  s->assert_formula(s->make_term(
      Equal, s->make_term(Mult, two, quotient), s->make_term(7, realsort)));

  // and an Int by a Real: (/ i 2.0) is 3/2 for i = 3
  Term i = s->make_symbol("i", intsort);
  s->assert_formula(s->make_term(Equal, i, s->make_term(3, intsort)));
  s->assert_formula(
      s->make_term(Equal,
                   s->make_term(Mult, two, s->make_term(Div, i, two)),
                   s->make_term(3, realsort)));

  // with i fixed, nothing is left to choose, so this is sat exactly when both
  // equations hold; dividing as Ints would make them 6 = 7 and 2 = 3
  EXPECT_TRUE(s->check_sat().is_sat());
}

INSTANTIATE_TEST_SUITE_P(,
                         IntRealArithmeticTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { THEORY_INT, THEORY_REAL })),
                         ConfigName());

}  // namespace
