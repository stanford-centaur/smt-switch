/*********************                                                        */
/*! \file unit-op.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for ops.
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitPrimOpTests);
class UnitPrimOpTests : public ::testing::Test,
                        // passing the PrimOp enum as a size_t
                        public ::testing::WithParamInterface<size_t>
{
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTests);
class UnitTests : public ::testing::Test,
                  public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
  }
  SmtSolver s;
  Sort boolsort, bvsort, funsort;
};

TEST_P(UnitPrimOpTests, GetArity)
{
  PrimOp po = static_cast<PrimOp>(GetParam());
  ASSERT_NO_THROW(get_arity(po));
}

TEST_P(UnitPrimOpTests, ToString)
{
  PrimOp po = static_cast<PrimOp>(GetParam());
  ASSERT_NO_THROW(::smt::to_string(po));
}

TEST_P(UnitTests, FunOp)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  ASSERT_EQ(fx->get_op(), Apply);
}

TEST_P(UnitTests, IndexedOps1)
{
  Term x = s->make_symbol("x", bvsort);
  Op ext = Op(Extract, 2, 0);
  Term ext_x = s->make_term(ext, x);
  ASSERT_EQ(ext_x->get_op(), ext);

  Op rep = Op(Repeat, 2);
  Term rep_x = s->make_term(rep, x);
  // some solvers rewrite -- might be concats
  // but we can check the sort
  ASSERT_EQ(rep_x->get_sort()->get_width(), 8);

  Op se = Op(Sign_Extend, 4);
  Term se_x = s->make_term(se, x);
  ASSERT_EQ(se_x->get_sort()->get_width(), 8);
  Op op = se_x->get_op();
  TermVec children;
  for (auto tt : se_x)
  {
    children.push_back(tt);
  }
  Term se_x_rebuilt = s->make_term(op, children);
  ASSERT_EQ(se_x_rebuilt, se_x);
}

TEST_P(UnitTests, RotateOps)
{
  Term x = s->make_symbol("x", bvsort);
  Term rotate_left = s->make_term(Op(Rotate_Left, 2), x);
  Term rotate_right = s->make_term(Op(Rotate_Right, 2), rotate_left);
  s->assert_formula(s->make_term(Distinct, x, rotate_right));
  Result r = s->check_sat();
  ASSERT_TRUE(r.is_unsat());
}

TEST_P(UnitTests, BoolFun)
{
  Term b = s->make_symbol("b", boolsort);
  Sort boolfunsort = s->make_sort(FUNCTION, SortVec{ boolsort, boolsort });
  Term f = s->make_symbol("f", boolfunsort);
  Term fb = s->make_term(Apply, f, b);
}

TEST_P(UnitTests, MultiArgFun)
{
  SortVec argsorts(7, bvsort);
  // return sort
  argsorts.push_back(boolsort);
  Sort multiargsort = s->make_sort(FUNCTION, argsorts);
  Term f = s->make_symbol("f", multiargsort);

  TermVec args1{f};
  TermVec args2{f};
  for (size_t i = 0; i < 7; i++)
  {
    args1.push_back(s->make_symbol("x" + std::to_string(i), bvsort));
    args2.push_back(s->make_symbol("y" + std::to_string(i), bvsort));
  }

  Term res = s->make_term(Apply, args1);
  ASSERT_EQ(res, s->make_term(Apply, args1));

  Term res2 = s->make_term(Apply, args2);
  ASSERT_NE(res, res2);
  ASSERT_EQ(res2, s->make_term(Apply, args2));
}

INSTANTIATE_TEST_SUITE_P(ParameterizedPrimOp,
                         UnitPrimOpTests,
                         testing::Range((size_t)0,
                                        static_cast<size_t>(NUM_OPS_AND_NULL)));

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnit,
                         UnitTests,
                         testing::ValuesIn(filter_solver_configurations({ TERMITER })));

}  // namespace smt_tests
