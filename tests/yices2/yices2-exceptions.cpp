/*!
 * \file yices2-exceptions.cpp
 * \brief The exceptions Yices2 throws for failed calls and refused operators.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Yices keeps the code of its last error until it is cleared, so a failed
 * call that is reported without clearing it would be reported again by the
 * next call that checks for one.
 */

#include <gtest/gtest.h>

#include "exceptions.h"
#include "ops.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "yices2_factory.h"

using namespace smt;

TEST(Yices2Exceptions, LaterCallsDoNotReportAnEarlierError)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  EXPECT_THROW(s->make_sort(BV, 0), InternalSolverException);
  EXPECT_NO_THROW(s->make_sort(BV, 4));

  SmtSolver fresh = Yices2SolverFactory::create(false);
  EXPECT_NO_THROW(fresh->make_sort(BV, 4));
}

TEST(Yices2Exceptions, MissingOperatorsAreNotImplemented)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort bvsort = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);

  Term p = s->make_param("p", bvsort);
  Term body = s->make_term(Equal, p, y);

  EXPECT_THROW(s->make_term(Apply_Tester, x, y), NotImplementedException);
  EXPECT_THROW(s->make_term(Forall, p, body), NotImplementedException);
}

TEST(Yices2Exceptions, MisappliedOperatorsAreIncorrectUsage)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort bvsort = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);

  EXPECT_THROW(s->make_term(Op(Not, 3), x), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Op(Extract, 3, 0), x, y), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Concat, x), IncorrectUsageException);
}
