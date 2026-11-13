/*!
 * \file btor-opts.cpp
 * \brief Tests for setting options through boolector
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <string>
#include <unordered_set>

#include "smt-switch/boolector_factory.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

using namespace smt;
using namespace std;

TEST(BtorOptTest3, NonStandardOpt)
{
  // tests an option that's boolector specific
  SmtSolver s = BoolectorSolverFactory::create(false);
  EXPECT_NO_THROW(s->set_opt("nondestr-subst", "true"));
}

TEST(BtorOptTest4, IncorrectOption)
{
  // tests an option that shouldn't exist
  SmtSolver s = BoolectorSolverFactory::create(false);
  EXPECT_THROW(s->set_opt("totally-made-up-option", "true"),
               NotImplementedException);
}

TEST(BtorOpts, NumericValueOutOfRange)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  // not a number, more than 32 bits, and more than this option allows
  for (const char * value : { "abc", "-1", "4294967296", "5" })
  {
    EXPECT_THROW(s->set_opt("nondestr-subst", value), IncorrectUsageException)
        << value;
  }
}

TEST(BtorOpts, BaseContextOffAccepted)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  EXPECT_NO_THROW(s->set_opt("base-context-1", "false"));
  EXPECT_EQ(s->get_context_level(), 0);
}

TEST(BtorOpts, ModelsTurnedOffAgain)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("produce-models", "true");
  s->set_opt("produce-models", "false");
  Sort bv8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bv8);
  s->assert_formula(s->make_term(Equal, x, s->make_term(1, bv8)));
  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_THROW(s->get_value(x), Exception);
}

TEST(BtorOpts, IncrementalTurnedOffAgain)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("incremental", "true");
  s->set_opt("incremental", "false");
  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_THROW(s->check_sat(), Exception);
}

TEST(BtorOpts, UnsatAssumptionsTurnedOffAgain)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("incremental", "true");
  s->set_opt("produce-unsat-assumptions", "true");
  s->set_opt("produce-unsat-assumptions", "false");
  Term a = s->make_symbol("a", s->make_sort(BOOL));
  s->assert_formula(s->make_term(Not, a));
  ASSERT_TRUE(s->check_sat_assuming({ a }).is_unsat());
  UnorderedTermSet core;
  EXPECT_THROW(s->get_unsat_assumptions(core), IncorrectUsageException);
  // with unsat assumptions off, incremental can be turned off too
  EXPECT_NO_THROW(s->set_opt("incremental", "false"));
}

TEST(BtorOpts, IncrementalAloneGivesNoUnsatAssumptions)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("incremental", "true");
  Term a = s->make_symbol("a", s->make_sort(BOOL));
  s->assert_formula(s->make_term(Not, a));
  ASSERT_TRUE(s->check_sat_assuming({ a }).is_unsat());
  UnorderedTermSet core;
  EXPECT_THROW(s->get_unsat_assumptions(core), IncorrectUsageException);
}

TEST(BtorOpts, UnsatAssumptionsKeepIncrementalOn)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("produce-unsat-assumptions", "true");
  EXPECT_THROW(s->set_opt("incremental", "false"), NotImplementedException);

  // the refusal left incremental on, so the assumptions still work
  Term a = s->make_symbol("a", s->make_sort(BOOL));
  s->assert_formula(s->make_term(Not, a));
  ASSERT_TRUE(s->check_sat_assuming({ a }).is_unsat());
  UnorderedTermSet core;
  s->get_unsat_assumptions(core);
  EXPECT_EQ(core, UnorderedTermSet({ a }));
}

TEST(BtorOpts, UnsatAssumptionsNeedIncremental)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("incremental", "false");
  EXPECT_THROW(s->set_opt("produce-unsat-assumptions", "true"),
               NotImplementedException);
}

TEST(BtorOpts, ResetForgetsUnsatAssumptions)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("produce-unsat-assumptions", "true");
  s->reset();
  EXPECT_NO_THROW(s->set_opt("incremental", "false"));
}
