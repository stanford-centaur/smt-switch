/*!
 * \file test-real.cpp
 * \brief Tests for nonlinear real arithmetic.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include <gtest/gtest.h>

#include "available_solvers.h"
#include "smt.h"

using namespace smt;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(RealArithmeticTests);
class RealArithmeticTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    s->set_opt("incremental", "true");
    // whether a solver handles nonlinear arithmetic can depend on how it was
    // built: Yices2 needs MCSAT for it
    try
    {
      s->set_logic("QF_NRA");
    }
    catch (const IncorrectUsageException & e)
    {
      GTEST_SKIP() << e.what();
    }
    realsort = s->make_sort(REAL);
    x = s->make_symbol("x", realsort);
    y = s->make_symbol("y", realsort);
  }
  SmtSolver s;
  Sort realsort;
  Term x, y;
};

TEST_P(RealArithmeticTests, ProductAndSum)
{
  // x * y = 6 and x + y = 5 with x > y have the one solution x = 3, y = 2
  s->assert_formula(
      s->make_term(Equal, s->make_term(Mult, x, y), s->make_term(6, realsort)));
  s->assert_formula(
      s->make_term(Equal, s->make_term(Plus, x, y), s->make_term(5, realsort)));
  s->assert_formula(s->make_term(Gt, x, y));
  ASSERT_TRUE(s->check_sat().is_sat());

  // checked as the only solution rather than read from the model, which
  // some backends give as an Int
  s->push();
  s->assert_formula(
      s->make_term(Or,
                   s->make_term(Distinct, x, s->make_term(3, realsort)),
                   s->make_term(Distinct, y, s->make_term(2, realsort))));
  EXPECT_TRUE(s->check_sat().is_unsat());
  s->pop();
}

// x * x = 2 has only irrational solutions, so the value of x is not asked
// for: Yices2 cannot turn the algebraic number it finds into a term
TEST_P(RealArithmeticTests, IrrationalSolution)
{
  if (GetParam().solver_enum == MSAT)
  {
    GTEST_SKIP() << "MathSAT does not answer x * x = 2 within minutes";
  }
  s->assert_formula(
      s->make_term(Equal, s->make_term(Mult, x, x), s->make_term(2, realsort)));
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST_P(RealArithmeticTests, NoSolution)
{
  s->assert_formula(
      s->make_term(Lt, s->make_term(Mult, x, x), s->make_term(0, realsort)));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

INSTANTIATE_TEST_SUITE_P(
    ,
    RealArithmeticTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_REAL })),
    ConfigName());

}  // namespace smt_tests
