/*********************                                                        */
/*! \file unit-solving-interface.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for solving interface.
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSolveTests);
class UnitSolveTests : public ::testing::Test,
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

TEST_P(UnitSolveTests, CheckSatAssuming)
{
  Term b1 = s->make_symbol("b1", boolsort);
  Term b2 = s->make_symbol("b2", boolsort);
  Term x = s->make_symbol("x", bvsort);

  Term nb2 = s->make_term(Not, b2);
  Term xeq0 = s->make_term(Equal, x, s->make_term(0, bvsort));
  Term nxeq0 = s->make_term(Not, xeq0);
  s->assert_formula(s->make_term(Implies, b1, xeq0));
  s->assert_formula(s->make_term(Implies, nb2, nxeq0));

  Result r;
  try
  {
    r = s->check_sat_assuming(TermVec{ xeq0, nb2 });
  }
  catch (IncorrectUsageException & e)
  {
    // mathsat is the only solver (so far)
    // to have the restriction that assumptions must be
    // (negated) boolean constants
    EXPECT_TRUE(s->get_solver_enum() == MSAT);
    r = s->check_sat_assuming(TermVec{ b1, nb2 });
    EXPECT_TRUE(r.is_unsat());
  }

  if (s->get_solver_enum() != GENERIC_SOLVER)
  {
    r = s->check_sat_assuming_list(TermList{ b1, nb2 });
    EXPECT_TRUE(r.is_unsat());

    r = s->check_sat_assuming_set(UnorderedTermSet{ b1, nb2 });
    EXPECT_TRUE(r.is_unsat());
  }
}

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSolveTests,
                         UnitSolveTests,
                         testing::ValuesIn(filter_solver_configurations({ TERMITER })));

}  // namespace smt_tests
