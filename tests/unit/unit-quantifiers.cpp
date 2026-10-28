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

#include "available_solvers.h"
#include "exceptions.h"
#include "gtest/gtest.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

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
class UnitQuantifierTests
    : public ::testing::Test,
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
class UnitQuantifierIterTests
    : public ::testing::Test,
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

TEST_P(UnitQuantifierIterTests, OpAndSort)
{
  // a param apiece, as Boolector binds a param in one quantifier only
  Term b = s->make_param("b", boolsort);
  Term c = s->make_param("c", boolsort);
  Term forallb = s->make_term(Forall, b, b);
  Term existsc = s->make_term(Exists, c, c);
  EXPECT_EQ(forallb->get_op(), Forall);
  EXPECT_EQ(forallb->get_sort(), boolsort);
  EXPECT_EQ(existsc->get_op(), Exists);
  EXPECT_EQ(existsc->get_sort(), boolsort);
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

// A bound variable named like a declared symbol is still another term, as
// SMT-LIB lets a binder shadow a declared name. Each formula says every
// value equals the symbol, so it is unsat; had the binder captured the
// symbol, it would read forall x . x = x and be sat. MathSAT answers
// unknown to it, however the variables are named.
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(Binders);
class Binders : public UnitQuantifierTests
{
 protected:
  // assert forall param . param = symbol and check it is not sat
  void expect_symbol_not_captured(const Term & param, const Term & symbol)
  {
    s->assert_formula(
        s->make_term(Forall, param, s->make_term(Equal, param, symbol)));
    EXPECT_FALSE(s->check_sat().is_sat());
  }
};

TEST_P(Binders, ParamNamedLikeEarlierSymbol)
{
  Term symbol = s->make_symbol("x", bvsort);
  Term param = s->make_param("x", bvsort);
  expect_symbol_not_captured(param, symbol);
}

TEST_P(Binders, SymbolNamedLikeEarlierParam)
{
  Term param = s->make_param("x", bvsort);
  Term symbol = s->make_symbol("x", bvsort);
  expect_symbol_not_captured(param, symbol);
}

TEST_P(Binders, NoParam)
{
  Term body = s->make_symbol("b", boolsort);
  EXPECT_THROW(s->make_term(Forall, body), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Exists, TermVec{ body }), IncorrectUsageException);
}

// binding a symbol would capture it, changing what the formula means
TEST_P(Binders, SymbolAsBinder)
{
  Term p = s->make_param("p", bvsort);
  Term q = s->make_param("q", bvsort);
  Term symbol = s->make_symbol("x", bvsort);
  Term body = s->make_term(Equal, p, symbol);
  EXPECT_THROW(s->make_term(Forall, symbol, body), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Exists, p, symbol, body), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Forall, TermVec{ p, q, symbol, body }),
               IncorrectUsageException);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedQuantifierIterTests,
    UnitQuantifierIterTests,
    testing::ValuesIn(filter_solver_configurations({ QUANTIFIERS, TERMITER })));

INSTANTIATE_TEST_SUITE_P(
    UnitQuantifiers,
    Binders,
    testing::ValuesIn(filter_solver_configurations({ QUANTIFIERS })),
    ConfigName());

}  // namespace
