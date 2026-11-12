/*!
 * \file btor-opts.cpp
 * \brief Tests for setting options through boolector
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <string>

#include "smt-switch/boolector_factory.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"

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
