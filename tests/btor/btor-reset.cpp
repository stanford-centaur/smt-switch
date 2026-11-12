/*!
 * \file btor-reset.cpp
 * \brief Tests for resetting a Boolector solver
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <string>

#include "smt-switch/boolector_factory.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"

using namespace smt;

TEST(BtorResetTest, BaseContext1AfterReset)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("incremental", "true");
  s->set_opt("base-context-1", "true");
  s->reset();

  // reset() returns to the startup state, so the option is set again
  s->set_opt("incremental", "true");
  s->set_opt("base-context-1", "true");
  s->assert_formula(s->make_term(false));
  s->reset_assertions();
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST(BtorResetTest, BaseContext1KeepsItsLevelFromPop)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("incremental", "true");
  s->set_opt("base-context-1", "true");
  s->assert_formula(s->make_term(false));
  EXPECT_THROW(s->pop(), IncorrectUsageException);
  EXPECT_EQ(s->get_context_level(), 0);
  // the assertion is still there, and reset_assertions still removes it
  EXPECT_TRUE(s->check_sat().is_unsat());
  s->reset_assertions();
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST(BtorResetTest, BaseContext1HidesItsLevel)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("incremental", "true");
  s->set_opt("base-context-1", "true");
  EXPECT_EQ(s->get_context_level(), 0);

  // pop_all leaves the hidden context, which reset_assertions pops
  s->push();
  s->pop_all();
  EXPECT_EQ(s->get_context_level(), 0);
  s->assert_formula(s->make_term(false));
  s->reset_assertions();
  EXPECT_EQ(s->get_context_level(), 0);
  EXPECT_TRUE(s->check_sat().is_sat());
}
