/*!
 * \file bzla-term-lifetime.cpp
 * \brief Tests that Bitwuzla terms and sorts outlive what created them.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * A Bitwuzla term or sort points into its term manager, which each term
 * and sort keeps alive, so one held past its solver or past a reset() can
 * still be used on its own and released.
 */

#include <gtest/gtest.h>

#include "bitwuzla_factory.h"
#include "smt.h"

using namespace smt;

TEST(BzlaTermLifetime, TermsOutliveTheirSolver)
{
  Sort bv;
  Term x, xpx;
  {
    SmtSolver s = BitwuzlaSolverFactory::create(false);
    bv = s->make_sort(BV, 4);
    x = s->make_symbol("x", bv);
    xpx = s->make_term(BVAdd, x, x);
  }
  EXPECT_EQ(xpx->to_string(), "(bvadd x x)");
  EXPECT_EQ(xpx->get_sort(), bv);
  for (const Term & child : xpx)
  {
    EXPECT_EQ(child, x);
  }
}

TEST(BzlaTermLifetime, TermsOutliveReset)
{
  SmtSolver s = BitwuzlaSolverFactory::create(false);
  Sort bv = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bv);
  Term xpx = s->make_term(BVAdd, x, x);
  s->reset();

  // the new term manager works alongside the old one
  Term b = s->make_symbol("b", s->make_sort(BOOL));
  s->assert_formula(b);
  EXPECT_TRUE(s->check_sat().is_sat());
  EXPECT_EQ(xpx->to_string(), "(bvadd x x)");
}
