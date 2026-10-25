/*!
 * \file unit-set-logic.cpp
 * \brief Tests that set_logic loses nothing, whether accepted or refused.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * SMT-LIB allows one logic, before any declaration, assertion, push or
 * check. Solvers accept more than that, and smt-switch allows what each
 * one allows, so a later set_logic may be accepted or refused with
 * IncorrectUsageException. One it accepts must keep what was made before.
 */

#include <gtest/gtest.h>

#include "available_solvers.h"
#include "smt.h"

using namespace smt;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SetLogic);
class SetLogic : public ::testing::Test,
                 public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override { s = create_solver(GetParam()); }

  SmtSolver s;
};

TEST_P(SetLogic, AcceptedFirst)
{
  s->set_logic("QF_UFBV");
  Sort bv = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bv);
  s->assert_formula(s->make_term(Equal, x, s->make_term(3, bv)));
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST_P(SetLogic, AfterDeclaration)
{
  s->set_logic("QF_UFBV");
  Sort bv = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bv);
  try
  {
    s->set_logic("QF_UFBV");
  }
  catch (IncorrectUsageException &)
  {
    return;
  }
  s->assert_formula(s->make_term(Equal, x, s->make_term(3, bv)));
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST_P(SetLogic, AfterAssertion)
{
  s->set_logic("QF_UFBV");
  Sort bv = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bv);
  Term three = s->make_term(3, bv);
  s->assert_formula(s->make_term(Equal, x, three));
  try
  {
    s->set_logic("QF_UFBV");
  }
  catch (IncorrectUsageException &)
  {
    return;
  }
  s->assert_formula(s->make_term(Distinct, x, three));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST_P(SetLogic, AfterOption)
{
  s->set_opt("produce-models", "true");
  s->set_logic("QF_UFBV");
  Sort bv = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bv);
  Term three = s->make_term(3, bv);
  s->assert_formula(s->make_term(Equal, x, three));
  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_EQ(s->get_value(x), three);
}

TEST_P(SetLogic, BeforeOption)
{
  s->set_logic("QF_UFBV");
  // SMT-LIB allows produce-models only before the logic
  try
  {
    s->set_opt("produce-models", "true");
  }
  catch (IncorrectUsageException &)
  {
    return;
  }
  Sort bv = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bv);
  Term three = s->make_term(3, bv);
  s->assert_formula(s->make_term(Equal, x, three));
  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_EQ(s->get_value(x), three);
}

TEST_P(SetLogic, KeepsScopes)
{
  s->set_opt("incremental", "true");
  s->push();
  s->assert_formula(s->make_term(false));
  try
  {
    s->set_logic("QF_UFBV");
  }
  catch (IncorrectUsageException &)
  {
  }
  EXPECT_EQ(s->get_context_level(), 1);
  EXPECT_TRUE(s->check_sat().is_unsat());
  s->pop();
  EXPECT_EQ(s->get_context_level(), 0);
  EXPECT_TRUE(s->check_sat().is_sat());
}

INSTANTIATE_TEST_SUITE_P(
    ,
    SetLogic,
    testing::ValuesIn(filter_solver_configurations({ THEORY_BV })),
    ConfigName());

}  // namespace smt_tests
