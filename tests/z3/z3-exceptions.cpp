/*!
 * \file z3-exceptions.cpp
 * \brief The exceptions the Z3 backend throws for refused operators.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Z3 has every SMT-LIB operator, so one this backend refuses at an arity
 * SMT-LIB allows is missing glue, and one applied to an arity or a number of
 * indices SMT-LIB does not allow is misuse.
 */

#include <gtest/gtest.h>

#include "exceptions.h"
#include "ops.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "z3_factory.h"

using namespace smt;

TEST(Z3Exceptions, MissingOperatorsAreNotImplemented)
{
  SmtSolver s = Z3SolverFactory::create(false);
  Term x = s->make_symbol("x", s->make_sort(BV, 4));

  EXPECT_THROW(s->make_term(StrLen, x), NotImplementedException);
}

TEST(Z3Exceptions, MisappliedOperatorsAreIncorrectUsage)
{
  SmtSolver s = Z3SolverFactory::create(false);
  Sort bvsort = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);

  EXPECT_THROW(s->make_term(Op(Not, 3), x), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Rotate_Left, x, y), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Op(Extract, 3, 0), x, y), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Concat, x), IncorrectUsageException);
}
