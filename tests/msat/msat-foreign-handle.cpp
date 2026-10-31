/*!
 * \file msat-foreign-handle.cpp
 * \brief Tests that MathSAT refuses terms and sorts from another environment.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Each MathSAT solver has its own environment, and reset() replaces it, so
 * a term or sort made by another solver, or by the same one before a reset,
 * would be read by MathSAT as one of this environment's.
 */

#include <gtest/gtest.h>

#include "exceptions.h"
#include "interpolating_solver.h"
#include "msat_factory.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"

using namespace smt;

TEST(MsatForeignHandle, AnotherSolversTermsRefused)
{
  SmtSolver s = MsatSolverFactory::create(false);
  s->set_opt("produce-models", "true");
  SmtSolver other = MsatSolverFactory::create(false);
  Sort bv8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bv8);
  Sort other_bv8 = other->make_sort(BV, 8);
  Term y = other->make_symbol("y", other_bv8);
  Term p = other->make_term(Equal, y, y);
  Term f = other->make_symbol(
      "f", other->make_sort(FUNCTION, SortVec{ other_bv8, other_bv8 }));

  EXPECT_THROW(s->assert_formula(p), IncorrectUsageException);
  EXPECT_THROW(s->check_sat_assuming(TermVec{ p }), IncorrectUsageException);
  EXPECT_THROW(s->make_term(BVAdd, x, y), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Apply, f, x), IncorrectUsageException);
  EXPECT_THROW(s->substitute(x, { { x, y } }), IncorrectUsageException);
  EXPECT_THROW(s->substitute(x, { { y, x } }), IncorrectUsageException);
  EXPECT_THROW(s->substitute(y, { { x, x } }), IncorrectUsageException);
  Sort arr = s->make_sort(ARRAY, bv8, bv8);
  EXPECT_THROW(s->make_term(y, arr), IncorrectUsageException);

  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_THROW(s->get_value(y), IncorrectUsageException);
}

TEST(MsatForeignHandle, AnotherSolversAssertionRefused)
{
  SmtSolver s = MsatSolverFactory::create(false);
  SmtSolver other = MsatSolverFactory::create(false);
  Term a = s->make_symbol("a", s->make_sort(BOOL));
  Term b = other->make_symbol("b", other->make_sort(BOOL));
  s->assert_formula(a);

  EXPECT_THROW(s->assert_formula(other->make_term(Not, b)),
               IncorrectUsageException);
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST(MsatForeignHandle, AnotherSolversSortsRefused)
{
  SmtSolver s = MsatSolverFactory::create(false);
  SmtSolver other = MsatSolverFactory::create(false);
  Sort bv8 = s->make_sort(BV, 8);
  Sort other_bv8 = other->make_sort(BV, 8);
  Sort other_arr = other->make_sort(ARRAY, other_bv8, other_bv8);

  EXPECT_THROW(s->make_symbol("x", other_bv8), IncorrectUsageException);
  EXPECT_THROW(s->make_param("x", other_bv8), IncorrectUsageException);
  EXPECT_THROW(s->make_term(s->make_term(0, bv8), other_arr),
               IncorrectUsageException);
  EXPECT_THROW(s->make_sort(ARRAY, bv8, other_bv8), IncorrectUsageException);
  EXPECT_THROW(s->make_sort(FUNCTION, SortVec{ other_bv8, bv8 }),
               IncorrectUsageException);
  EXPECT_THROW(s->make_sort(FUNCTION, SortVec{ bv8, other_bv8 }),
               IncorrectUsageException);
}

TEST(MsatForeignHandle, HandlesFromBeforeResetRefused)
{
  SmtSolver s = MsatSolverFactory::create(false);
  Sort bv8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bv8);
  Term p = s->make_term(Equal, x, x);
  s->reset();

  EXPECT_THROW(s->assert_formula(p), IncorrectUsageException);
  EXPECT_THROW(s->make_symbol("y", bv8), IncorrectUsageException);
}

TEST(MsatForeignHandle, AnotherInterpolatorsTermsRefused)
{
  SmtInterpolator itp = MsatSolverFactory::create_interpolating_solver();
  SmtInterpolator other = MsatSolverFactory::create_interpolating_solver();
  Sort other_bv8 = other->make_sort(BV, 8);
  Term y = other->make_symbol("y", other_bv8);
  Term other_a = other->make_term(Equal, y, other->make_term(0, other_bv8));
  Term other_b = other->make_term(Equal, y, other->make_term(1, other_bv8));
  Sort bv8 = itp->make_sort(BV, 8);
  Term x = itp->make_symbol("x", bv8);
  Term a = itp->make_term(Equal, x, itp->make_term(0, bv8));
  Term b = itp->make_term(Equal, x, itp->make_term(1, bv8));

  Term out_I;
  EXPECT_THROW(itp->get_interpolant(a, other_b, out_I),
               IncorrectUsageException);
  EXPECT_THROW(itp->get_interpolant(other_a, b, out_I),
               IncorrectUsageException);
  EXPECT_TRUE(itp->get_interpolant(a, b, out_I).is_unsat());
}
