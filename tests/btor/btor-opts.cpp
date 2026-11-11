/*********************                                                        */
/*! \file btor-opts.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for setting options through boolector.
**
**
**/

#include <gtest/gtest.h>

#include <string>

#include "boolector_factory.h"
#include "exceptions.h"
#include "smt_defs.h"
#include "solver.h"

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
