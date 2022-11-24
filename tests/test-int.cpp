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
    intx = s->make_term(BV_To_Nat, bvx);
  }
  catch (SmtException & e)
  {
    std::cout << "Got exception when trying to apply BV_To_Nat: " << e.what()
              << std::endl;
    // it's fine if this op is not supported, just end the test
    return;
  }

  ASSERT_TRUE(intx);
  EXPECT_EQ(intx->get_sort(), intsort);
  EXPECT_EQ(intx->get_op(), BV_To_Nat);

  Term inty = s->make_symbol("inty", intsort);
  Term bvy = s->make_term(Op(Int_To_BV, 8), inty);
  EXPECT_EQ(bvy->get_sort(), bvsort);
  EXPECT_EQ(bvy->get_op(), Op(Int_To_BV, 8));
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverIntTests,
    IntTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_INT })));

}  // namespace smt_tests
