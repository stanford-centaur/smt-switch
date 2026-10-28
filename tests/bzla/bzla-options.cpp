/*!
 * \file bzla-options.cpp
 * \brief Tests when options can be set on a Bitwuzla solver.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Bitwuzla takes its options when the solver instance is created, on first
 * use, and ignores later changes, so set_opt must refuse them instead. A
 * query that needs no instance must not create one.
 */

#include <gtest/gtest.h>

#include <string>

#include "bitwuzla_factory.h"
#include "exceptions.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"

using namespace smt;

TEST(BzlaOptions, RefusedOnceSolving)
{
  SmtSolver s = BitwuzlaSolverFactory::create(false);
  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_THROW(s->set_opt("produce-models", "true"), IncorrectUsageException);
}

TEST(BzlaOptions, AcceptedAfterDump)
{
  SmtSolver s = BitwuzlaSolverFactory::create(false);
  s->dump_smt2(testing::TempDir() + "bzla-options.smt2");
  EXPECT_NO_THROW(s->set_opt("produce-models", "true"));
}

TEST(BzlaOptions, AcceptedAfterRefusedQuery)
{
  SmtSolver s = BitwuzlaSolverFactory::create(false);
  Term x = s->make_symbol("x", s->make_sort(BV, 8));
  ASSERT_THROW(s->get_value(x), IncorrectUsageException);
  EXPECT_NO_THROW(s->set_opt("produce-models", "true"));
}

TEST(BzlaOptions, TakenAgainAfterReset)
{
  SmtSolver s = BitwuzlaSolverFactory::create(false);
  ASSERT_TRUE(s->check_sat().is_sat());
  s->reset();
  ASSERT_NO_THROW(s->set_opt("produce-models", "true"));

  // the option takes effect: without it, get_value throws
  Sort bv8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bv8);
  Term one = s->make_term(1, bv8);
  s->assert_formula(s->make_term(Equal, x, one));
  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_EQ(s->get_value(x), one);
}
