/*!
 * \file z3-foreign-sort.cpp
 * \brief Tests that Z3 refuses sorts from another Z3 context.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Each Z3 solver has its own context, and Z3 would read a sort made in
 * another one as its own, building terms that fail later or corrupt the
 * context.
 */

#include <gtest/gtest.h>

#include "exceptions.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "z3_factory.h"

using namespace smt;

TEST(Z3ForeignSort, AnotherSolversSortsRefused)
{
  SmtSolver s = Z3SolverFactory::create(false);
  SmtSolver other = Z3SolverFactory::create(false);
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

TEST(Z3ForeignSort, AnotherSolversDatatypeSortsRefused)
{
  SmtSolver s = Z3SolverFactory::create(false);
  SmtSolver other = Z3SolverFactory::create(false);
  Sort other_bv8 = other->make_sort(BV, 8);
  DatatypeConstructorDecl other_c = other->make_datatype_constructor_decl("c");
  other->add_selector(other_c, "f", other_bv8);
  DatatypeDecl other_d = other->make_datatype_decl("D");
  other->add_constructor(other_d, other_c);
  Sort other_dt = other->make_sort(other_d);
  DatatypeConstructorDecl c = s->make_datatype_constructor_decl("c");

  EXPECT_THROW(s->add_selector(c, "f", other_bv8), IncorrectUsageException);
  EXPECT_THROW(s->get_constructor(other_dt, "c"), IncorrectUsageException);
  EXPECT_THROW(s->get_tester(other_dt, "c"), IncorrectUsageException);
  EXPECT_THROW(s->get_selector(other_dt, "c", "f"), IncorrectUsageException);
}
