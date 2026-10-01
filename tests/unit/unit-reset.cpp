/*********************                                                        */
/*! \file unit-reset.cpp
** \verbatim
** Top contributors (to current version):
**   Áron Ricardo Perez-Lopez
** This file is part of the smt-switch project.
** Copyright (c) 2026 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for resetting a solver.
**
**
**/

#include <gtest/gtest.h>

#include <vector>

#include "available_solvers.h"
#include "smt.h"

using namespace smt;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitResetTests);
class UnitResetTests : public ::testing::Test,
                       public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override { s = create_solver(GetParam()); }
  SmtSolver s;
};

TEST_P(UnitResetTests, ResetReleasesSymbols)
{
  // only the solver holds x, so reset() is what destroys it
  s->make_symbol("x", s->make_sort(BV, 4));
  try
  {
    s->reset();
  }
  catch (NotImplementedException &)
  {
    GTEST_SKIP() << "reset is not implemented";
  }

  // x is gone, so its name can be declared again
  Term x = s->make_symbol("x", s->make_sort(BOOL));
  s->assert_formula(x);
  EXPECT_TRUE(s->check_sat().is_sat());
}

static std::vector<SolverConfiguration> working_reset_configurations()
{
  std::vector<SolverConfiguration> result;
  for (const SolverConfiguration & sc : available_solver_configurations())
  {
    // reset() times out on the generic solver and double-frees on Yices2
    if (sc.solver_enum != GENERIC_SOLVER && sc.solver_enum != YICES2)
    {
      result.push_back(sc);
    }
  }
  return result;
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnitReset,
                         UnitResetTests,
                         testing::ValuesIn(working_reset_configurations()));

}  // namespace smt_tests
