/*!
 * \file btor-foreign-sort.cpp
 * \brief Tests that Boolector refuses sorts from another Boolector instance.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Boolector numbers sorts per instance, and reset() replaces the instance,
 * so a sort made by another solver, or by the same one before a reset, would
 * be read as this instance's sort of the same number.
 */

#include <gtest/gtest.h>

#include "boolector_factory.h"
#include "exceptions.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"

using namespace smt;

TEST(BtorForeignSort, AnotherSolversSortsRefused)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  SmtSolver other = BoolectorSolverFactory::create(false);
  Sort bv8 = s->make_sort(BV, 8);
  Sort other_bv8 = other->make_sort(BV, 8);
  Sort other_arr = other->make_sort(ARRAY, other_bv8, other_bv8);

  EXPECT_THROW(s->make_symbol("x", other_bv8), IncorrectUsageException);
  EXPECT_THROW(s->make_param("x", other_bv8), IncorrectUsageException);
  EXPECT_THROW(s->make_term(1, other_bv8), IncorrectUsageException);
  EXPECT_THROW(s->make_term(s->make_term(0, bv8), other_arr),
               IncorrectUsageException);
  EXPECT_THROW(s->make_sort(ARRAY, bv8, other_bv8), IncorrectUsageException);
  EXPECT_THROW(s->make_sort(FUNCTION, SortVec{ other_bv8, bv8 }),
               IncorrectUsageException);
}

TEST(BtorForeignSort, SortsFromBeforeResetRefused)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  Sort bv8 = s->make_sort(BV, 8);
  s->reset();

  EXPECT_THROW(s->make_symbol("x", bv8), IncorrectUsageException);
}
