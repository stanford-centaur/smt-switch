/*!
 * \file bzla-term-manager.cpp
 * \brief Tests that Bitwuzla refuses terms and sorts from another term
 * manager.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Each Bitwuzla solver has its own term manager, and reset() replaces it, so
 * a term or sort made by another solver, or by the same one before a reset,
 * cannot be used. That is a usage error, as on cvc5.
 */

#include <gtest/gtest.h>

#include <memory>
#include <string>

#include "bitwuzla_factory.h"
#include "exceptions.h"
#include "interpolating_solver.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"

using namespace smt;

TEST(BzlaTermManager, AnotherSolversTermsRefused)
{
  SmtSolver s = BitwuzlaSolverFactory::create(false);
  s->set_opt("produce-models", "true");
  SmtSolver other = BitwuzlaSolverFactory::create(false);
  Sort bv8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bv8);
  Sort other_bv8 = other->make_sort(BV, 8);
  Term y = other->make_symbol("y", other_bv8);
  Term p = other->make_term(Equal, y, y);

  EXPECT_THROW(s->assert_formula(p), IncorrectUsageException);
  EXPECT_THROW(s->check_sat_assuming(TermVec{ p }), IncorrectUsageException);
  EXPECT_THROW(s->make_term(BVAdd, x, y), IncorrectUsageException);
  EXPECT_THROW(s->substitute(x, { { x, y } }), IncorrectUsageException);
  EXPECT_THROW(s->substitute_terms({ y }, { { x, x } }),
               IncorrectUsageException);

  EXPECT_THROW(s->make_symbol("z", other_bv8), IncorrectUsageException);
  EXPECT_THROW(s->make_param("z", other_bv8), IncorrectUsageException);
  EXPECT_THROW(s->make_term(1, other_bv8), IncorrectUsageException);
  EXPECT_THROW(s->make_term("1", other_bv8), IncorrectUsageException);
  EXPECT_THROW(s->make_sort(ARRAY, bv8, other_bv8), IncorrectUsageException);
  EXPECT_THROW(s->make_sort(FUNCTION, SortVec{ other_bv8, bv8 }),
               IncorrectUsageException);
  Sort arr = s->make_sort(ARRAY, bv8, bv8);
  EXPECT_THROW(s->make_term(y, arr), IncorrectUsageException);

  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_THROW(s->get_value(y), IncorrectUsageException);
}

TEST(BzlaTermManager, TermsFromBeforeResetRefused)
{
  SmtSolver s = BitwuzlaSolverFactory::create(false);
  Sort bv8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bv8);
  Term p = s->make_term(Equal, x, x);
  s->reset();

  EXPECT_THROW(s->assert_formula(p), IncorrectUsageException);
  EXPECT_THROW(s->make_symbol("y", bv8), IncorrectUsageException);
}

TEST(BzlaTermManager, AnotherInterpolatorsTermsRefused)
{
  SmtInterpolator itp = BitwuzlaSolverFactory::create_interpolating_solver();
  SmtInterpolator other = BitwuzlaSolverFactory::create_interpolating_solver();
  Sort bv8 = other->make_sort(BV, 8);
  Term y = other->make_symbol("y", bv8);
  Term a = other->make_term(Equal, y, other->make_term(0, bv8));
  Term b = other->make_term(Equal, y, other->make_term(1, bv8));

  Term out_I;
  EXPECT_THROW(itp->get_interpolant(a, b, out_I), IncorrectUsageException);
}
