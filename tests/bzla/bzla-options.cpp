/*!
 * \file bzla-options.cpp
 * \brief Tests when options can be set on a Bitwuzla solver.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Bitwuzla takes its options when the solver instance is created, on first
 * use, and ignores later changes, so set_opt must refuse them instead.
 */

#include <gtest/gtest.h>

#include "bitwuzla_factory.h"
#include "smt.h"

using namespace smt;

TEST(BzlaOptions, RefusedOnceSolving)
{
  SmtSolver s = BitwuzlaSolverFactory::create(false);
  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_THROW(s->set_opt("produce-models", "true"), IncorrectUsageException);
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
