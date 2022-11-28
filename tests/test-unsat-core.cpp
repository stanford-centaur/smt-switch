/*********************                                                        */
/*! \file test-unsat-core.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for unsat core production.
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnsatCoreTests);
class UnsatCoreTests : public ::testing::Test,
                 public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    SolverConfiguration sc = GetParam();
    s = create_solver(sc);
    s->set_opt("incremental", "true");
    s->set_opt("produce-unsat-assumptions", "true");
    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 8);
  }
  SmtSolver s;
  Sort boolsort, bvsort;
};

// FIXME there's some issue with the Yices2 context object which
// fails if there are two separate tests using the unsat core feature

TEST_P(UnsatCoreTests, UnsatCore)
{
  // test that everything works in a fresh context
  s->push();
  Term a = s->make_symbol("a", boolsort);
  Term b = s->make_symbol("b", boolsort);
  Result r = s->check_sat_assuming({ a, b, s->make_term(Not, b) });
  ASSERT_TRUE(r.is_unsat());

  UnorderedTermSet core;
  s->get_unsat_assumptions(core);
  ASSERT_TRUE(core.size() > 1);

  // for solvers using assumptions under the hood,
  // make sure they are re-added correctly
  r = s->check_sat();
  ASSERT_TRUE(r.is_sat());
  // unsat core is only available after a call to check-sat-assuming, not
  // check-sat
  ASSERT_THROW(s->get_unsat_assumptions(core), SmtException);
}

TEST_P(UnsatCoreTests, UnsatCoreNonLit)
{
  // test that everything works in a fresh context
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);

  Term x_lt_y = s->make_term(BVUlt, x, y);
  Term x_ge_y = s->make_term(BVUge, x, y);

  Result r = s->check_sat_assuming({ x_lt_y, x_ge_y });
  ASSERT_TRUE(r.is_unsat());

  r = s->check_sat_assuming({x_lt_y});
  ASSERT_TRUE(r.is_sat());

  r = s->check_sat_assuming({x_lt_y, x_ge_y});
  ASSERT_TRUE(r.is_unsat());

  UnorderedTermSet core;
  s->get_unsat_assumptions(core);
  ASSERT_TRUE(core.size() > 1);
}

TEST_P(UnsatCoreTests, NoAssumptionsNeeded)
{
  Term a = s->make_symbol("a", boolsort);
  Term b = s->make_symbol("b", boolsort);
  // make unsat without assumptions
  s->assert_formula(a);
  Term nota = s->make_term(Not, a);
  s->assert_formula(nota);

  Result r = s->check_sat_assuming({ b });
  UnorderedTermSet core;
  s->get_unsat_assumptions(core);
  // a and not(a) were not in assumptions
  // so shouldn't show up in unsat assumptions
  ASSERT_TRUE(core.find(a) == core.end());
  ASSERT_TRUE(core.find(nota) == core.end());
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverUnsatCoreTests,
    UnsatCoreTests,
    testing::ValuesIn(filter_solver_configurations({ UNSAT_CORE })));

}  // namespace smt_tests
