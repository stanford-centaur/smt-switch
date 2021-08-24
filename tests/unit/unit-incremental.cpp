/*********************                                                        */
/*! \file unit-incremental.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for incremental solving interface.
**
**
**/

#include <utility>
#include <vector>

#include "available_solvers.h"
#include "exceptions.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class UnitIncrementalTests
    : public ::testing::Test,
      public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("incremental", "true");
    s->set_opt("produce-models", "true");
    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
  }
  SmtSolver s;
  Sort boolsort, bvsort;
};

TEST_P(UnitIncrementalTests, ContextLevel)
{
  Term a = s->make_symbol("a", boolsort);
  Term b = s->make_symbol("b", boolsort);
  s->assert_formula(a);

  EXPECT_EQ(s->get_context_level(), 0);

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  s->push();
  EXPECT_EQ(s->get_context_level(), 1);
  s->assert_formula(s->make_term(Not, b));
  r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  s->push();
  EXPECT_EQ(s->get_context_level(), 2);
  s->assert_formula(s->make_term(Or, s->make_term(Not, a), b));

  r = s->check_sat();
  ASSERT_TRUE(r.is_unsat());

  s->pop();
  EXPECT_EQ(s->get_context_level(), 1);
  r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  s->pop();
  EXPECT_EQ(s->get_context_level(), 0);
  s->assert_formula(b);
  r = s->check_sat();
  ASSERT_TRUE(r.is_sat());
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedUnitIncrementalTests,
    UnitIncrementalTests,
    testing::ValuesIn(filter_solver_configurations({ TERMITER })));

}  // namespace smt_tests
