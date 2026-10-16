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

#include "boolector_factory.h"
#include "smt.h"

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
