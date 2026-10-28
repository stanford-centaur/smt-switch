/*********************                                                        */
/*! \file unit-reset-assertions.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for resetting assertions
**        Note: there's a special case for Boolector
**        Boolector does not currently support reset_assertions natively. But,
**        it can be approximated by doing all solving at context level 1, and
**        popping all the contexts to reset assertions.
**
**
**/

#include "available_solvers.h"
#include "exceptions.h"
#include "gtest/gtest.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitResetAssertionsTests);
class UnitResetAssertionsTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    SolverConfiguration sc = GetParam();
    SolverEnum se = sc.solver_enum;
    s = create_solver(sc);
    s->set_opt("produce-models", "true");
    s->set_opt("incremental", "true");

    if (se == BTOR)
    {
      // special option for boolector
      // not enabled by default because it can affect performance
      s->set_opt("base-context-1", "true");
    }

    bvsort = s->make_sort(BV, 8);
  }
  SmtSolver s;
  Sort bvsort;
};

TEST_P(UnitResetAssertionsTests, ResetAssertions)
{
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term xpy = s->make_term(BVAdd, x, y);
  Term xmy = s->make_term(BVSub, x, y);

  Term constraint = s->make_term(Equal, xpy, xmy);
  s->assert_formula(constraint);

  Result r = s->check_sat();
  EXPECT_TRUE(r.is_sat());

  Term zero = s->make_term(0, bvsort);
  Term make_unsat = s->make_term(
      And, s->make_term(Distinct, x, zero), s->make_term(Distinct, y, zero));
  Term half_max = s->make_term(128, bvsort);
  make_unsat = s->make_term(And,
                            make_unsat,
                            s->make_term(And,
                                         s->make_term(BVUlt, x, half_max),
                                         s->make_term(BVUlt, y, half_max)));
  s->push(2);
  s->assert_formula(make_unsat);
  r = s->check_sat();
  ASSERT_TRUE(r.is_unsat());
  s->pop(2);

  r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  s->assert_formula(make_unsat);
  r = s->check_sat();
  ASSERT_TRUE(r.is_unsat());

  s->reset_assertions();
  r = s->check_sat();
  ASSERT_TRUE(r.is_sat());
}

TEST_P(UnitResetAssertionsTests, ResetAssertionsDropsContexts)
{
  Term f = s->make_term(false);
  s->assert_formula(f);
  ASSERT_TRUE(s->check_sat().is_unsat());
  s->push(2);

  s->reset_assertions();
  EXPECT_EQ(s->get_context_level(), 0);

  // the solver has to agree, or this pop leaves f asserted
  s->push();
  s->assert_formula(f);
  s->pop();
  EXPECT_EQ(s->get_context_level(), 0);
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST_P(UnitResetAssertionsTests, ResetAssertionsKeepsDeclarations)
{
  Term x = s->make_symbol("x", bvsort);
  Term f =
      s->make_symbol("f", s->make_sort(FUNCTION, SortVec{ bvsort, bvsort }));
  s->assert_formula(s->make_term(Equal, s->make_term(Apply, f, x), x));
  ASSERT_TRUE(s->check_sat().is_sat());

  s->reset_assertions();

  // both are still declared: usable, and their names taken
  Term three = s->make_term(3, bvsort);
  s->assert_formula(s->make_term(Equal, s->make_term(Apply, f, x), three));
  s->assert_formula(s->make_term(Equal, x, three));
  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_EQ(s->get_value(x), three);
  EXPECT_THROW(s->make_symbol("x", bvsort), IncorrectUsageException);
}

// only run this test if built with Boolector
#ifdef BUILD_BTOR
TEST(UnitBtorResetAssertionsTests, ResetAssertionsException)
{
  // Boolector backend does not support reset_assertions by default
  // Underlying solver boolector does not have reset_assertions
  // but we can approximate it using solving contexts, but this
  // might impact performance
  SolverConfiguration sc(BTOR, false);
  SmtSolver s = create_solver(sc);
  s->set_opt("produce-models", "true");
  s->set_opt("incremental", "true");
  Sort bvsort = s->make_sort(BV, 8);

  Term f = s->make_term(false);
  s->assert_formula(f);

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_unsat());

  ASSERT_THROW(s->reset_assertions(), NotImplementedException);
}
#endif

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnitResetAssertions,
                         UnitResetAssertionsTests,
                         testing::ValuesIn(available_solver_configurations()));

}  // namespace
