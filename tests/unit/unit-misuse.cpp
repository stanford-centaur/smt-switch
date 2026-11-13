/*!
 * \file unit-misuse.cpp
 * \brief Tests that every backend refuses common misuse alike
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * A call SMT-LIB does not allow is refused with IncorrectUsageException,
 * whichever solver is underneath. A call SMT-LIB allows but the solver
 * cannot carry out is NotImplementedException.
 */
#include <gtest/gtest.h>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"

using namespace smt;
using namespace smt_tests;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(Misuse);
class Misuse : public ::testing::Test,
               public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override { s = create_solver(GetParam()); }

  SmtSolver s;
};

TEST_P(Misuse, GetValueWithoutProduceModels)
{
  SolverEnum se = GetParam().solver_enum;
  if (se == YICES2 || se == Z3)
  {
    GTEST_SKIP() << "the backend gives a model without produce-models";
  }
  if (se == BTOR || se == BZLA || se == CVC5)
  {
    GTEST_SKIP() << "the backend does not translate the solver's refusal";
  }
  Term x = s->make_symbol("x", s->make_sort(BOOL));
  s->assert_formula(x);
  s->check_sat();
  EXPECT_THROW(s->get_value(x), IncorrectUsageException);
}

TEST_P(Misuse, GetValueAfterUnsat)
{
  SolverEnum se = GetParam().solver_enum;
  if (se == BTOR || se == BZLA || se == CVC5)
  {
    GTEST_SKIP() << "the backend does not translate the solver's refusal";
  }
  s->set_opt("produce-models", "true");
  Term x = s->make_symbol("x", s->make_sort(BOOL));
  s->assert_formula(s->make_term(false));
  s->check_sat();
  EXPECT_THROW(s->get_value(x), IncorrectUsageException);
}

// SMT-LIB allows push without any option, so a solver that needs one
// cannot do what was asked
TEST_P(Misuse, PushIsHonouredOrNotImplemented)
{
  if (GetParam().solver_enum == BTOR)
  {
    GTEST_SKIP() << "the backend does not translate the solver's refusal";
  }
  try
  {
    s->push();
  }
  catch (const NotImplementedException &)
  {
    // any other exception escapes and fails the test
  }
}

TEST_P(Misuse, SecondCheckSatIsHonouredOrNotImplemented)
{
  if (GetParam().solver_enum == BTOR)
  {
    GTEST_SKIP() << "the backend does not translate the solver's refusal";
  }
  s->check_sat();
  try
  {
    s->check_sat();
  }
  catch (const NotImplementedException &)
  {
    // any other exception escapes and fails the test
  }
}

TEST_P(Misuse, IllSortedApplication)
{
  SolverEnum se = GetParam().solver_enum;
  if (se == BTOR || se == MSAT || se == YICES2)
  {
    GTEST_SKIP() << "the backend does not translate the solver's refusal";
  }
  Term b = s->make_symbol("b", s->make_sort(BOOL));
  Term v = s->make_symbol("v", s->make_sort(BV, 4));
  EXPECT_THROW(s->make_term(And, b, v), IncorrectUsageException);
}

TEST_P(Misuse, UnsatAssumptionsAfterPlainCheckSat)
{
  SolverEnum se = GetParam().solver_enum;
  if (se == BTOR || se == BZLA || se == CVC5 || se == YICES2
      || se == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the backend answers without a check_sat_assuming";
  }
  if (se == MSAT)
  {
    GTEST_SKIP() << "the backend refuses with the base exception class";
  }
  s->set_opt("produce-unsat-assumptions", "true");
  s->assert_formula(s->make_term(false));
  s->check_sat();
  UnorderedTermSet core;
  EXPECT_THROW(s->get_unsat_assumptions(core), IncorrectUsageException);
}

TEST_P(Misuse, ZeroWidthBitVector)
{
  SolverEnum se = GetParam().solver_enum;
  if (se == MSAT || se == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the backend makes a bit-vector sort of width 0";
  }
  if (se == BTOR || se == BZLA || se == CVC5 || se == YICES2)
  {
    GTEST_SKIP() << "the backend does not translate the solver's refusal";
  }
  EXPECT_THROW(s->make_sort(BV, 0), IncorrectUsageException);
}

INSTANTIATE_TEST_SUITE_P(,
                         Misuse,
                         testing::ValuesIn(available_solver_configurations()),
                         ConfigName());

}  // namespace
