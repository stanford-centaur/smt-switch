/*!
 * \file z3-set-logic.cpp
 * \brief Tests that Z3's set_logic loses nothing made before it.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * A logic picks a Z3 solver's tactic, so it takes a new solver. That is
 * safe only before the first assertion, check or push; declarations live
 * in the context and survive it.
 */

#include <gtest/gtest.h>

#include "smt.h"
#include "z3_factory.h"

using namespace smt;

namespace {

TEST(Z3SetLogic, RefusedAfterAssertion)
{
  SmtSolver s = Z3SolverFactory::create(false);
  s->assert_formula(s->make_term(false));
  ASSERT_TRUE(s->check_sat().is_unsat());
  EXPECT_THROW(s->set_logic("QF_UF"), IncorrectUsageException);
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST(Z3SetLogic, RefusedInAScope)
{
  SmtSolver s = Z3SolverFactory::create(false);
  s->push();
  s->assert_formula(s->make_term(false));
  EXPECT_THROW(s->set_logic("QF_UF"), IncorrectUsageException);
  EXPECT_EQ(s->get_context_level(), 1);
  EXPECT_TRUE(s->check_sat().is_unsat());
  s->pop();
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST(Z3SetLogic, AcceptedAfterDeclarations)
{
  SmtSolver s = Z3SolverFactory::create(false);
  Term x = s->make_symbol("x", s->make_sort(BOOL));
  s->set_logic("QF_UF");
  s->assert_formula(s->make_term(And, x, s->make_term(Not, x)));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST(Z3SetLogic, SecondLogicRefused)
{
  SmtSolver s = Z3SolverFactory::create(false);
  s->set_logic("QF_UF");
  EXPECT_THROW(s->set_logic("QF_UF"), IncorrectUsageException);
}

TEST(Z3SetLogic, UnknownLogicRefused)
{
  SmtSolver s = Z3SolverFactory::create(false);
  EXPECT_THROW(s->set_logic("NOT_A_LOGIC"), IncorrectUsageException);
}

}  // namespace
