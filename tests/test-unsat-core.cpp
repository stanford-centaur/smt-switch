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

class UnsatCoreTests : public ::testing::Test,
                 public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    SolverConfiguration sc = GetParam();
    s = create_solver(sc);
    s->set_opt("incremental", "true");
    if (sc.solver_enum == GENERIC_SOLVER)
    {
      s->set_opt("produce-unsat-assumptions", "true");
    }
    else
    {
      s->set_opt("produce-unsat-assumptions", "true");
    }
    boolsort = s->make_sort(BOOL);
  }
  SmtSolver s;
  Sort boolsort;
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

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverUnsatCoreTests,
    UnsatCoreTests,
    testing::ValuesIn(filter_solver_configurations({ UNSAT_CORE })));

}  // namespace smt_tests
