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

#include <cstdint>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

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

INSTANTIATE_TEST_SUITE_P(
    ,
    IntArithmeticTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_INT })),
    ConfigName());

}  // namespace smt_tests
