/*********************                                                        */
/*! \file test-logging-solver.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for LoggingSolver infrastructure.
**
**
**/

#include <memory>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "logging_solver.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(LoggingTests);
class LoggingTests : public ::testing::Test,
                     public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    // IMPORTANT : make sure not to use doubly nested LoggingSolvers
    // can mess things up
    // Thus, need to use the "lite" version of solvers
    // before wrapping with a LoggingSolver
    s = make_shared<LoggingSolver>(create_solver(GetParam()));
    s->set_opt("produce-models", "true");
    bvsort4 = s->make_sort(BV, 4);
    bvsort8 = s->make_sort(BV, 8);
    arraysort = s->make_sort(ARRAY, bvsort4, bvsort8);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort4, bvsort8 });

    x = s->make_symbol("x", bvsort4);
    y = s->make_symbol("y", bvsort4);
    zero = s->make_term(0, bvsort4);
    one = s->make_term(1, bvsort4);
  }
  SmtSolver s;
  Sort bvsort4, bvsort8, arraysort, funsort;
  Term x, y, zero, one;
};

TEST_P(LoggingTests, Children)
{
  EXPECT_TRUE(x->get_op().is_null());
  EXPECT_TRUE(y->is_symbolic_const());
  EXPECT_FALSE(y->is_value());

  Term xp1 = s->make_term(BVAdd, x, one);
  EXPECT_EQ(xp1->get_op(), BVAdd);
  TermVec children;
  for (auto tt : xp1)
  {
    children.push_back(tt);
  }
  EXPECT_EQ(children[0], x);
  EXPECT_EQ(children[1], one);
}

TEST_P(LoggingTests, HashConsing)
{
  Term xp1 = s->make_term(BVAdd, x, one);
  // Check hash-consing using comparison of underlying pointers
  Term xp1_2 = s->make_term(BVAdd, x, one);
  EXPECT_EQ(xp1.get(), xp1_2.get());
}

TEST_P(LoggingTests, Sorts)
{
  Term cond = s->make_term(BVUge, x, zero);
  EXPECT_EQ(cond->get_sort()->get_sort_kind(), BOOL);
  Term relu = s->make_term(Ite, cond, x, zero);
  EXPECT_EQ(relu->get_sort(), x->get_sort());
}

TEST_P(LoggingTests, ConstantSorts)
{
  Term t = s->make_term(true);
  Term f = s->make_term(false);
  EXPECT_NE(t, f);
  EXPECT_EQ(t, t);

  Sort bvsort1 = s->make_sort(BV, 1);
  Term bv0 = s->make_term(0, bvsort1);
  Term bv1 = s->make_term(1, bvsort1);
  EXPECT_NE(bv0, bv1);
  EXPECT_EQ(bv1, bv1);

  EXPECT_NE(f, bv0);
  EXPECT_NE(f, bv1);
  EXPECT_NE(t, bv0);
  EXPECT_NE(t, bv1);

  EXPECT_EQ(t->get_sort()->get_sort_kind(), BOOL);
  EXPECT_EQ(bv0->get_sort()->get_sort_kind(), BV);
  EXPECT_EQ(bv1->get_sort()->get_width(), 1);
}

TEST_P(LoggingTests, Compare)
{
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);
  Term fx2 = s->make_term(Apply, f, x);
  EXPECT_EQ(fx, fx2);

  Term fy = s->make_term(Apply, f, y);
  EXPECT_NE(fx, fy);

  Term x_eq_y = s->make_term(Equal, x, y);
  Term x_eq_y2 = s->make_term(Equal, x, y);
  EXPECT_EQ(x_eq_y, x_eq_y2);

  // LoggingTerms do no rewriting or normalization
  // you always get exactly what you created
  Term y_eq_x = s->make_term(Equal, y, x);
  EXPECT_NE(x_eq_y, y_eq_x);

  s->assert_formula(x_eq_y);

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  // compare values
  // they should be hash-consed correctly in LoggingSolver
  // so that comparison works as expected
  Term xv = s->get_value(x);
  Term yv = s->get_value(y);
  EXPECT_EQ(xv, yv);

  Term fxv = s->get_value(fx);
  Term fxv2 = s->get_value(fx2);
  Term fyv = s->get_value(fy);
  EXPECT_EQ(fxv, fxv2);
  EXPECT_EQ(fxv, fyv);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverLoggingTests,
    LoggingTests,
    testing::ValuesIn(available_solver_configurations()));

}  // namespace smt_tests
