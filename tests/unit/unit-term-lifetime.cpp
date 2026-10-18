/*!
 * \file unit-term-lifetime.cpp
 * \brief Tests that terms, sorts and child iterators outlive what made them.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * A term or sort held past its solver's destruction, or past a reset(),
 * must still answer questions about itself and be released safely, and an
 * iterator over a term's children must still yield them after the term is
 * gone.
 */

#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "available_solvers.h"
#include "smt.h"

using namespace smt;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(TermLifetimeTests);
class TermLifetimeTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
};

TEST_P(TermLifetimeTests, TermsOutliveTheirSolver)
{
  const SolverConfiguration & sc = GetParam();
  if (!sc.is_logging_solver && sc.solver_enum == MSAT)
  {
    GTEST_SKIP() << "MathSAT terms point into the environment their solver "
                    "destroys, so using one afterwards crashes";
  }
  Sort bv;
  Term x, y, xpy;
  std::string x_text;
  {
    SmtSolver s = create_solver(GetParam());
    bv = s->make_sort(BV, 4);
    x = s->make_symbol("x", bv);
    y = s->make_symbol("y", bv);
    xpy = s->make_term(BVAdd, x, y);
    x_text = x->to_string();
  }
  EXPECT_EQ(xpy->get_sort(), bv);
  EXPECT_EQ(x->to_string(), x_text);
  EXPECT_TRUE(y->is_symbolic_const());
}

TEST_P(TermLifetimeTests, TermsOutliveReset)
{
  const SolverConfiguration & sc = GetParam();
  if (sc.solver_enum == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "reset() times out on the generic solver";
  }
  if (!sc.is_logging_solver && sc.solver_enum == MSAT)
  {
    GTEST_SKIP() << "MathSAT's reset() destroys the environment its terms "
                    "point into, so using one afterwards crashes";
  }
  SmtSolver s = create_solver(GetParam());
  Sort bv = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bv);
  Term y = s->make_symbol("y", bv);
  Term xpy = s->make_term(BVAdd, x, y);
  std::string x_text = x->to_string();
  s->reset();

  // the solver keeps working after the reset
  Term b = s->make_symbol("b", s->make_sort(BOOL));
  s->assert_formula(b);
  EXPECT_TRUE(s->check_sat().is_sat());
  EXPECT_EQ(xpy->get_sort(), bv);
  EXPECT_EQ(x->to_string(), x_text);
  EXPECT_TRUE(y->is_symbolic_const());
}

TEST_P(TermLifetimeTests, ChildIteratorsOutliveTheirTerm)
{
  SmtSolver s = create_solver(GetParam());
  Sort bv = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bv);
  Term y = s->make_symbol("y", bv);
  Term z = s->make_symbol("z", bv);
  // the children are not symbols, so only the term holds them
  std::vector<std::string> expected;
  TermIter it, end;
  {
    Term t = s->make_term(
        BVAdd, s->make_term(BVMul, x, y), s->make_term(BVMul, x, z));
    for (TermIter i = t->begin(); i != t->end(); ++i)
    {
      expected.push_back((*i)->to_string());
    }
    it = t->begin();
    end = t->end();
  }
  std::vector<std::string> children;
  for (; it != end; ++it)
  {
    children.push_back((*it)->to_string());
  }
  EXPECT_EQ(children, expected);
}

INSTANTIATE_TEST_SUITE_P(
    ,
    TermLifetimeTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_BV })),
    ConfigName());

}  // namespace smt_tests
