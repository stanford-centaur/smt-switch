/*********************                                                        */
/*! \file btor-reset.cpp
** \verbatim
** Top contributors (to current version):
**   Áron Ricardo Perez-Lopez
** This file is part of the smt-switch project.
** Copyright (c) 2026 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for resetting a Boolector solver.
**
**
**/

#include <gtest/gtest.h>

#include <string>

#include "boolector_factory.h"
#include "smt.h"

using namespace smt;

TEST(BtorResetTest, ResetClearsContextLevel)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("incremental", "true");
  s->push(2);
  s->reset();
  EXPECT_EQ(s->get_context_level(), 0);

  // the fresh instance has to agree, or this pop goes below its base
  s->set_opt("incremental", "true");
  s->push();
  s->pop();
  EXPECT_EQ(s->get_context_level(), 0);
}

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

TEST(BtorResetTest, TimeLimitAfterReset)
{
  // the new instance needs the termination callback too, or a time limit
  // set after reset() does nothing
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("time-limit", "0.1");
  s->reset();
  s->set_opt("time-limit", "0.1");

  // a pigeonhole problem far too hard to finish inside the limit
  Sort bvsort = s->make_sort(BV, 6);
  TermVec vars;
  for (size_t i = 0; i < 65; ++i)
  {
    vars.push_back(s->make_symbol("x" + std::to_string(i), bvsort));
  }
  for (size_t i = 0; i < vars.size(); ++i)
  {
    for (size_t j = i + 1; j < vars.size(); ++j)
    {
      s->assert_formula(s->make_term(Distinct, vars[i], vars[j]));
    }
  }

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_unknown());
  EXPECT_EQ(r.get_explanation(), "Time limit reached.");
}
