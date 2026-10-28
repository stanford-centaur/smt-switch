/*!
 * \file yices2-queries.cpp
 * \brief Tests Yices2's model and core queries before a usable check.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * A query with no check to answer from must refuse without making the
 * context, which would fix the logic and options, and without handing
 * Yices a model that is not there.
 */

#include <gtest/gtest.h>

#include "exceptions.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"
#include "yices2_factory.h"

using namespace smt;

namespace {

TEST(Yices2Queries, GetValueBeforeCheckThrows)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Term x = s->make_symbol("x", s->make_sort(BOOL));
  EXPECT_THROW(s->get_value(x), IncorrectUsageException);
}

TEST(Yices2Queries, GetValueAfterUncheckedAssertionThrows)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Term x = s->make_symbol("x", s->make_sort(BOOL));
  s->assert_formula(x);
  EXPECT_THROW(s->get_value(x), IncorrectUsageException);
}

TEST(Yices2Queries, FailedQueryLeavesLogicSettable)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  UnorderedTermSet core;
  EXPECT_THROW(s->get_unsat_assumptions(core), IncorrectUsageException);
  EXPECT_NO_THROW(s->set_logic("QF_BV"));
}

}  // namespace
