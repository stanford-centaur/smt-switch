
/*********************                                           */
/*! \file unit-term-id.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for Term unique ids
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

class UnitTermIdTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    s->set_opt("incremental", "true");

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    a = s->make_symbol("a", boolsort);
    b = s->make_symbol("b", boolsort);
    x = s->make_symbol("x", bvsort);
    y = s->make_symbol("y", bvsort);
    one = s->make_term(1, bvsort);
  }
  SmtSolver s;
  Sort boolsort, bvsort;
  Term a, b, x, y, one;
};

TEST_P(UnitTermIdTests, BasicTest)
{
  EXPECT_EQ(a->get_id(), a->get_id());
  EXPECT_EQ(x->get_id(), x->get_id());

  EXPECT_NE(a->get_id(), b->get_id());
  EXPECT_NE(x->get_id(), y->get_id());
  EXPECT_NE(x->get_id(), one->get_id());

  Term a_and_b = s->make_term(And, a, b);
  EXPECT_NE(b->get_id(), a_and_b->get_id());

  Term a_and_b_2 = s->make_term(And, a, b);
  EXPECT_EQ(a_and_b->get_id(), a_and_b_2->get_id());

  Term xp1 = s->make_term(BVAdd, x, one);
  EXPECT_NE(x->get_id(), xp1->get_id());

  Term xp1_2 = s->make_term(BVAdd, x, one);
  EXPECT_EQ(xp1->get_id(), xp1_2->get_id());

  Term yp1 = s->make_term(BVAdd, y, one);
  EXPECT_NE(y->get_id(), yp1->get_id());

  Term yp1_2 = s->make_term(BVAdd, y, one);
  EXPECT_EQ(yp1->get_id(), yp1->get_id());
}

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitTermIdTests,
                         UnitTermIdTests,
                         testing::ValuesIn(available_solver_configurations()));

}  // namespace smt_tests
