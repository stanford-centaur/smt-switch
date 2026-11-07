/*!
 * \file z3-exceptions.cpp
 * \brief The exceptions the Z3 backend throws.
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
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"
#include "z3_factory.h"

using namespace smt;

TEST(Z3Exceptions, MissingOperatorsAreNotImplemented)
{
  SmtSolver s = Z3SolverFactory::create(false);
  Term x = s->make_symbol("x", s->make_sort(BV, 4));

  EXPECT_THROW(s->make_term(StrLen, x), NotImplementedException);
}

TEST(Z3Exceptions, LambdaModelValueHasNoOp)
{
  SmtSolver s = Z3SolverFactory::create(false);
  s->set_opt("produce-models", "true");
  Sort intsort = s->make_sort(INT);
  Term a = s->make_symbol("a", s->make_sort(ARRAY, intsort, intsort));
  Term i = s->make_param("i", intsort);
  // an array that maps every index to itself, which Z3 can only give as a
  // lambda
  s->assert_formula(s->make_term(
      Forall, i, s->make_term(Equal, s->make_term(Select, a, i), i)));
  ASSERT_TRUE(s->check_sat().is_sat());

  EXPECT_THROW(s->get_value(a)->get_op(), NotImplementedException);
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

TEST(Z3Exceptions, FunctionHasNoChildToDereference)
{
  SmtSolver s = Z3SolverFactory::create(false);
  Sort bvsort = s->make_sort(BV, 4);
  Term f = s->make_symbol("f", s->make_sort(FUNCTION, { bvsort, bvsort }));

  EXPECT_THROW(*f->begin(), IncorrectUsageException);
}

TEST(Z3Exceptions, ConstantArrayNeedsAnArraySort)
{
  SmtSolver s = Z3SolverFactory::create(false);
  Sort bvsort = s->make_sort(BV, 8);

  EXPECT_THROW(s->make_term(s->make_term(0, bvsort), bvsort),
               IncorrectUsageException);
}
