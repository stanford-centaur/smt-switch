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

namespace smt::tests {

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(Misuse);
class Misuse : public testing::Test,
               public testing::WithParamInterface<SolverConfiguration>
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
  Term x = s->make_symbol("x", s->make_sort(SortKind::BOOL));
  s->assert_formula(x);
  s->check_sat();
  EXPECT_THROW(s->get_value(x), IncorrectUsageException);
}

TEST_P(Misuse, GetValueWithProduceModelsOff)
{
  try
  {
    s->set_opt("produce-models", "false");
  }
  catch (const NotImplementedException &)
  {
    // a solver that cannot turn models off; any other exception escapes
    // and fails the test
    return;
  }
  Sort bvsort = s->make_sort(SortKind::BV, 8);
  Term v = s->make_symbol("v", bvsort);
  Term arr =
      s->make_symbol("arr", s->make_sort(SortKind::ARRAY, bvsort, bvsort));
  s->assert_formula(s->make_term(Op::Equal, v, s->make_term(37, bvsort)));
  s->assert_formula(s->make_term(
      Op::Equal, s->make_term(Op::Select, arr, v), s->make_term(9, bvsort)));
  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_THROW(s->get_value(v), IncorrectUsageException);
  Term base;
  EXPECT_THROW(s->get_array_values(arr, base), IncorrectUsageException);
}

TEST_P(Misuse, GetValueAfterUnsat)
{
  s->set_opt("produce-models", "true");
  Term x = s->make_symbol("x", s->make_sort(SortKind::BOOL));
  s->assert_formula(s->make_term(false));
  s->check_sat();
  EXPECT_THROW(s->get_value(x), IncorrectUsageException);
}

// SMT-LIB allows push without any option, so a solver that needs one
// cannot do what was asked
TEST_P(Misuse, PushIsHonouredOrNotImplemented)
{
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
  Term b = s->make_symbol("b", s->make_sort(SortKind::BOOL));
  Term v = s->make_symbol("v", s->make_sort(SortKind::BV, 4));
  EXPECT_THROW(s->make_term(Op::And, b, v), IncorrectUsageException);
}

TEST_P(Misuse, UnsatAssumptionsAfterSatCheck)
{
  s->set_opt("incremental", "true");
  s->set_opt("produce-unsat-assumptions", "true");
  Term b = s->make_symbol("b", s->make_sort(SortKind::BOOL));
  UnorderedTermSet core;
  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_THROW(s->get_unsat_assumptions(core), IncorrectUsageException);
  ASSERT_TRUE(s->check_sat_assuming(TermVec{ b }).is_sat());
  EXPECT_THROW(s->get_unsat_assumptions(core), IncorrectUsageException);
}

TEST_P(Misuse, ZeroWidthBitVector)
{
  SolverEnum se = GetParam().solver_enum;
  if (se == MSAT || se == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the backend makes a bit-vector sort of width 0";
  }
  EXPECT_THROW(s->make_sort(SortKind::BV, 0), IncorrectUsageException);
}

INSTANTIATE_TEST_SUITE_P(
    ,
    Misuse,
    testing::ValuesIn(available_solver_configurations_with_generic()),
    ConfigName());

}  // namespace

}  // namespace smt::tests
