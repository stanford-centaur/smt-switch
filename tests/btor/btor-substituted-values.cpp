/*!
 * \file btor-substituted-values.cpp
 * \brief Tests that Boolector terms simplified to values by a substitution
 *        are values
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Boolector substitutes the symbols an assertion fixes when it checks, so a
 * term made before the check can become a value afterwards.
 */
#include <gtest/gtest.h>

#include "smt-switch/boolector_factory.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

using namespace smt;

TEST(BtorSubstitutedValues, BitVector)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  Sort bvsort4 = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bvsort4);
  Term y = s->make_symbol("y", bvsort4);
  Term sum = s->make_term(BVAdd, x, y);
  s->assert_formula(s->make_term(Equal, x, s->make_term(1, bvsort4)));
  s->assert_formula(s->make_term(Equal, y, s->make_term(2, bvsort4)));
  ASSERT_TRUE(s->check_sat().is_sat());

  EXPECT_TRUE(sum->is_value());
  EXPECT_EQ(sum->to_int(), 3);
  EXPECT_FALSE(x->is_value());
}

TEST(BtorSubstitutedValues, Array)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  Sort bvsort4 = s->make_sort(BV, 4);
  Sort arrsort = s->make_sort(ARRAY, bvsort4, bvsort4);
  Term zero = s->make_term(0, bvsort4);
  Term c = s->make_symbol("c", s->make_sort(BOOL));
  Term a = s->make_symbol("a", arrsort);
  Term ite = s->make_term(Ite, c, s->make_term(zero, arrsort), a);
  Term store = s->make_term(Store, ite, zero, s->make_term(1, bvsort4));
  s->assert_formula(c);
  ASSERT_TRUE(s->check_sat().is_sat());

  EXPECT_TRUE(ite->is_value());
  EXPECT_TRUE(store->is_value());
}
