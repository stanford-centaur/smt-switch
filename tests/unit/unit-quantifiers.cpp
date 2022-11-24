/*********************                                                        */
/*! \file unit-quantifiers.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for quantifiers.
**
**
**/

#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

// Gets all bound variables, stores them in out_vars and returns the body
Term recover_quant(const Term & quant_term, TermVec & out_vars)
{
  Term body = quant_term;
  Op op = body->get_op();
  TermVec children;
  while (op == Forall || op == Exists)
  {
    children.clear();
    children.insert(children.end(), body->begin(), body->end());
    body = children.back();
    op = body->get_op();
    children.pop_back();
    for (const auto & cc : children)
    {
      out_vars.push_back(cc);
    }
  }
  return body;
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitQuantifierTests);
class UnitQuantifierTests : public ::testing::Test,
                            public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
  }
  SmtSolver s;
  Sort boolsort, bvsort, funsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitQuantifierIterTests);
class UnitQuantifierIterTests : public ::testing::Test,
                                public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
  }
  SmtSolver s;
  Sort boolsort, bvsort, funsort;
};

TEST_P(UnitQuantifierIterTests, BoolTrivialUnsat)
{
  Term b = s->make_param("b", boolsort);
  // parameters are considered symbols but not symbolic constants
  ASSERT_TRUE(b->is_param());
  ASSERT_TRUE(b->is_symbol());
  ASSERT_FALSE(b->is_symbolic_const());
  ASSERT_FALSE(b->is_value());
  // forall b . b
  Term forallb = s->make_term(Forall, b, b);
  ASSERT_EQ(forallb->get_op(), Forall);
  s->assert_formula(forallb);
  Result r = s->check_sat();
  ASSERT_TRUE(!r.is_sat());
}

TEST_P(UnitQuantifierIterTests, QuantifierTraversal)
{
  if (!GetParam().is_logging_solver && s->get_solver_enum() == Z3)
  {
    // Z3 backend cannot traverse quantifier structure yet
    return;
  }
  Term b = s->make_param("b", boolsort);
  Term x = s->make_param("x", bvsort);
  Term f = s->make_symbol("f", funsort);

  Term fx = s->make_term(Apply, f, x);
  Term bimpfxeq0 = s->make_term(
      Implies, b, s->make_term(Equal, fx, s->make_term(0, bvsort)));
  Term forallbx = s->make_term(Forall, { b, x, bimpfxeq0 });
  ASSERT_EQ(forallbx->get_sort(), boolsort);
  TermVec vars;
  Term body = recover_quant(forallbx, vars);
  ASSERT_EQ(vars.size(), 2);
  ASSERT_EQ(vars[0], b);
  ASSERT_EQ(vars[1], x);
  ASSERT_EQ(body, bimpfxeq0);
}

TEST_P(UnitQuantifierIterTests, QuantifierFunCheck)
{
  Term b = s->make_param("b", boolsort);
  Term x = s->make_param("x", bvsort);
  Term f = s->make_symbol("f", funsort);

  Term fx = s->make_term(Apply, f, x);
  Term fx_eq_0 = s->make_term(Equal, fx, s->make_term(0, bvsort));
  Term existsx = s->make_term(Exists, x, fx_eq_0);
  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());
}

INSTANTIATE_TEST_SUITE_P(ParameterizedQuantifierIterTests,
                         UnitQuantifierIterTests,
                         testing::ValuesIn(filter_solver_configurations({ QUANTIFIERS,
                                                                 TERMITER })));

}  // namespace smt_tests
