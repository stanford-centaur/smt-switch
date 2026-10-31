/*!
 * \file z3-foreign-term.cpp
 * \brief Tests that Z3 refuses terms from another Z3 context.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Each Z3 solver has its own context, and Z3 would read a term made in
 * another one as its own, failing inside Z3 or building terms that mix the
 * two contexts.
 */

#include <gtest/gtest.h>

#include "exceptions.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"
#include "z3_factory.h"

using namespace smt;

TEST(Z3ForeignTerm, AnotherSolversTermsRefused)
{
  SmtSolver s = Z3SolverFactory::create(false);
  SmtSolver other = Z3SolverFactory::create(false);
  Sort bv8 = s->make_sort(BV, 8);
  Sort arr = s->make_sort(ARRAY, bv8, bv8);
  Sort fun = s->make_sort(FUNCTION, SortVec{ bv8, bv8 });
  Term x = s->make_symbol("x", bv8);
  Term f = s->make_symbol("f", fun);
  Sort other_bv8 = other->make_sort(BV, 8);
  Term other_x = other->make_symbol("x", other_bv8);
  Term other_arr =
      other->make_symbol("a", other->make_sort(ARRAY, other_bv8, other_bv8));
  Term other_f = other->make_symbol(
      "f", other->make_sort(FUNCTION, SortVec{ other_bv8, other_bv8 }));
  Term other_p = other->make_term(Equal, other_x, other_x);

  EXPECT_THROW(s->assert_formula(other_p), IncorrectUsageException);
  EXPECT_THROW(s->check_sat_assuming(TermVec{ other_p }),
               IncorrectUsageException);
  EXPECT_THROW(s->make_term(other_x, arr), IncorrectUsageException);
  EXPECT_THROW(s->make_term(BVNot, other_x), IncorrectUsageException);
  EXPECT_THROW(s->make_term(BVAdd, x, other_x), IncorrectUsageException);
  EXPECT_THROW(s->make_term(BVAdd, other_x, x), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Apply, other_f, x), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Apply, f, other_x), IncorrectUsageException);
  EXPECT_THROW(s->substitute(other_x, UnorderedTermMap{}),
               IncorrectUsageException);
  EXPECT_THROW(s->substitute(x, UnorderedTermMap{ { x, other_x } }),
               IncorrectUsageException);
  EXPECT_THROW(s->substitute(x, UnorderedTermMap{ { other_x, x } }),
               IncorrectUsageException);

  ASSERT_EQ(s->check_sat(), Result(SAT));
  Term base;
  EXPECT_THROW(s->get_value(other_x), IncorrectUsageException);
  EXPECT_THROW(s->get_array_values(other_arr, base), IncorrectUsageException);
}
