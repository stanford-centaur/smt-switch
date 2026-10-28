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
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"

using namespace smt;
using namespace smt_tests;

namespace {

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
  s->reset();

  // x is gone, so its name can be declared again
  Term x = s->make_symbol("x", s->make_sort(BOOL));
  s->assert_formula(x);
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST_P(UnitResetTests, ResetDropsAssertions)
{
  s->set_opt("incremental", "true");
  s->push();
  s->assert_formula(s->make_term(false));
  ASSERT_TRUE(s->check_sat().is_unsat());

  s->reset();
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST_P(UnitResetTests, ResetClearsContextLevel)
{
  s->set_opt("incremental", "true");
  s->push(2);
  s->reset();
  EXPECT_EQ(s->get_context_level(), 0);

  // the solver after the reset agrees, or this pop goes below its base
  s->set_opt("incremental", "true");
  s->push();
  s->pop();
  EXPECT_EQ(s->get_context_level(), 0);
}

TEST_P(UnitResetTests, ResetLeavesOtherSolversAlone)
{
  SmtSolver other = create_solver(GetParam());
  other->set_opt("produce-models", "true");
  Term b = other->make_symbol("b", other->make_sort(BOOL));
  other->assert_formula(b);
  s->reset();

  ASSERT_TRUE(other->check_sat().is_sat());
  EXPECT_EQ(other->get_value(b), other->make_term(true));
}

// One argument each, so on Yices2 the function and the array have one type
TEST_P(UnitResetTests, FunctionNameReusedForArray)
{
  Sort bvsort = s->make_sort(BV, 4);
  Term old_f =
      s->make_symbol("f", s->make_sort(FUNCTION, SortVec{ bvsort, bvsort }));
  Term old_fx = s->make_term(Apply, old_f, s->make_symbol("x", bvsort));
  s->reset();

  // terms held from before the reset read as they did
  EXPECT_EQ(old_f->get_sort()->get_sort_kind(), FUNCTION);
  EXPECT_EQ(old_fx->get_op(), Apply);

  bvsort = s->make_sort(BV, 4);
  Term f = s->make_symbol("f", s->make_sort(ARRAY, bvsort, bvsort));
  Term x = s->make_symbol("x", bvsort);
  EXPECT_EQ(f->get_sort()->get_sort_kind(), ARRAY);
  EXPECT_EQ(s->make_term(Select, f, x)->get_op(), Select);
}

TEST_P(UnitResetTests, ArrayNameReusedForFunction)
{
  Sort bvsort = s->make_sort(BV, 4);
  Term old_f = s->make_symbol("f", s->make_sort(ARRAY, bvsort, bvsort));
  Term old_fx = s->make_term(Select, old_f, s->make_symbol("x", bvsort));
  s->reset();

  // terms held from before the reset read as they did
  EXPECT_EQ(old_f->get_sort()->get_sort_kind(), ARRAY);
  EXPECT_EQ(old_fx->get_op(), Select);

  bvsort = s->make_sort(BV, 4);
  Term f =
      s->make_symbol("f", s->make_sort(FUNCTION, SortVec{ bvsort, bvsort }));
  Term x = s->make_symbol("x", bvsort);
  EXPECT_EQ(f->get_sort()->get_sort_kind(), FUNCTION);
  EXPECT_EQ(s->make_term(Apply, f, x)->get_op(), Apply);
}

TEST_P(UnitResetTests, FunctionNameReusedByNextSolver)
{
  {
    Sort bvsort = s->make_sort(BV, 4);
    s->make_symbol("f", s->make_sort(FUNCTION, SortVec{ bvsort, bvsort }));
  }
  // with nothing left using it, Yices2 frees its terms and reuses their ids
  s = nullptr;
  s = create_solver(GetParam());

  Sort bvsort = s->make_sort(BV, 4);
  Term f = s->make_symbol("f", s->make_sort(ARRAY, bvsort, bvsort));
  Term x = s->make_symbol("x", bvsort);
  EXPECT_EQ(f->get_sort()->get_sort_kind(), ARRAY);
  EXPECT_EQ(s->make_term(Select, f, x)->get_op(), Select);
}

static std::vector<SolverConfiguration> working_reset_configurations()
{
  std::vector<SolverConfiguration> result;
  for (const SolverConfiguration & sc : available_solver_configurations())
  {
    // reset() times out on the generic solver
    if (sc.solver_enum != GENERIC_SOLVER)
    {
      result.push_back(sc);
    }
  }
  return result;
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnitReset,
                         UnitResetTests,
                         testing::ValuesIn(working_reset_configurations()));

}  // namespace
