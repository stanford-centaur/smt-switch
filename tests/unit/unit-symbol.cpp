/*********************                                                        */
/*! \file unit-symbol.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for symbol terms.
**
**
**/

#include <gtest/gtest.h>

#include <memory>
#include <string>
#include <vector>

#include "available_solvers.h"
#include "exceptions.h"
#include "ops.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSymbolTests);
class UnitSymbolTests : public ::testing::Test,
                        public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  }
  SmtSolver s;
  Sort boolsort, bvsort, funsort, arrsort;
};

TEST_P(UnitSymbolTests, RedeclareException)
{
  Term b = s->make_symbol("b", boolsort);
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term a = s->make_symbol("a", arrsort);

  EXPECT_THROW(s->make_symbol("b", boolsort), IncorrectUsageException);
  EXPECT_THROW(s->make_symbol("x", bvsort), IncorrectUsageException);
  EXPECT_THROW(s->make_symbol("f", funsort), IncorrectUsageException);
  EXPECT_THROW(s->make_symbol("a", arrsort), IncorrectUsageException);
}

TEST_P(UnitSymbolTests, GetSymbol)
{
  Term b = s->make_symbol("b", boolsort);
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term a = s->make_symbol("a", arrsort);

  EXPECT_EQ(b, s->get_symbol("b"));
  EXPECT_EQ(x, s->get_symbol("x"));
  EXPECT_EQ(f, s->get_symbol("f"));
  EXPECT_EQ(a, s->get_symbol("a"));

  string funky_name = "strange @ name!";
  string funky_name_fun = "strange Fun _ name$";
  Term funky_sym = s->make_symbol(funky_name, boolsort);
  Term funky_sym_fun = s->make_symbol(funky_name_fun, funsort);

  EXPECT_EQ(funky_sym, s->get_symbol(funky_name));
  EXPECT_EQ(funky_sym_fun, s->get_symbol(funky_name_fun));

  EXPECT_THROW(s->get_symbol("nonexistent_symbol"), IncorrectUsageException);
}

TEST_P(UnitSymbolTests, SymbolName)
{
  Term b = s->make_symbol("b", boolsort);
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term a = s->make_symbol("a", arrsort);

  EXPECT_EQ(b->get_symbol_name(), "b");
  EXPECT_EQ(x->get_symbol_name(), "x");
  EXPECT_EQ(f->get_symbol_name(), "f");
  EXPECT_EQ(a->get_symbol_name(), "a");
}

// Names SMT-LIB prints in bars come back without them.
TEST_P(UnitSymbolTests, QuotedSymbolName)
{
  Term spaced = s->make_symbol("a b", boolsort);
  Term reserved = s->make_symbol("let", boolsort);
  Term digit = s->make_symbol("1x", bvsort);
  Term fun = s->make_symbol("strange Fun _ name$", funsort);

  EXPECT_EQ(spaced->get_symbol_name(), "a b");
  EXPECT_EQ(reserved->get_symbol_name(), "let");
  EXPECT_EQ(digit->get_symbol_name(), "1x");
  EXPECT_EQ(fun->get_symbol_name(), "strange Fun _ name$");
}

// Symbols made after a push keep their names. By default, Boolector's API
// prefixes such a name with its count of pushes and pops, as in BTOR_1@x,
// which smt-switch's Boolector backend avoids by naming the symbol directly.
TEST_P(UnitSymbolTests, SymbolNameAfterPush)
{
  s->set_opt("incremental", "true");
  Term prefixed = s->make_symbol("BTOR_1@x", bvsort);
  s->push();
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term a = s->make_symbol("a", arrsort);

  EXPECT_EQ(prefixed->get_symbol_name(), "BTOR_1@x");
  EXPECT_EQ(x->get_symbol_name(), "x");
  EXPECT_EQ(f->get_symbol_name(), "f");
  EXPECT_EQ(a->get_symbol_name(), "a");
  EXPECT_EQ(x->to_string(), "x");
}

TEST_P(UnitSymbolTests, EmptySymbolName)
{
  if (GetParam().solver_enum == MSAT)
  {
    GTEST_SKIP() << "MathSAT refuses an empty name, so the backend declares "
                    "the symbol as || instead";
  }
  if (GetParam().solver_enum == Z3)
  {
    GTEST_SKIP() << "Z3 makes an empty name its null symbol, named <null>";
  }
  Term empty = s->make_symbol("", boolsort);
  EXPECT_EQ(empty->get_symbol_name(), "");
}

TEST_P(UnitSymbolTests, NonSymbolHasNoSymbolName)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);

  EXPECT_THROW(s->make_term(1, bvsort)->get_symbol_name(),
               IncorrectUsageException);
  EXPECT_THROW(s->make_term(BVNot, x)->get_symbol_name(),
               IncorrectUsageException);
  EXPECT_THROW(s->make_term(Apply, f, x)->get_symbol_name(),
               IncorrectUsageException);
}

TEST_P(UnitSymbolTests, GetSymbolOnFreshSolver)
{
  // the fixture's sorts are made already, so this solver has made nothing
  SmtSolver fresh = create_solver(GetParam());
  EXPECT_THROW(fresh->get_symbol("x"), IncorrectUsageException);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnitSymbol,
                         UnitSymbolTests,
                         testing::ValuesIn(available_solver_configurations()));

}  // namespace
