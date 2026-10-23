/*!
 * \file cvc5-set-logic.cpp
 * \brief Tests that cvc5's refusals of set_logic report misuse.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * cvc5 takes one logic, before the first assertion, check or push. A call
 * out of that order, or with a logic cvc5 does not know, is the caller's
 * mistake, not a solver failure.
 */

#include <gtest/gtest.h>

#include "cvc5_factory.h"
#include "smt.h"

using namespace smt;

namespace {

TEST(Cvc5SetLogic, SecondLogicRefused)
{
  SmtSolver s = Cvc5SolverFactory::create(false);
  s->set_logic("QF_UF");
  EXPECT_THROW(s->set_logic("QF_UF"), IncorrectUsageException);
}

TEST(Cvc5SetLogic, RefusedAfterAssertion)
{
  SmtSolver s = Cvc5SolverFactory::create(false);
  s->assert_formula(s->make_term(false));
  EXPECT_THROW(s->set_logic("QF_UF"), IncorrectUsageException);
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST(Cvc5SetLogic, UnknownLogicRefused)
{
  SmtSolver s = Cvc5SolverFactory::create(false);
  EXPECT_THROW(s->set_logic("NOT_A_LOGIC"), IncorrectUsageException);
}

}  // namespace
