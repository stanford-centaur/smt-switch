/*!
 * \file unit-symbol.cpp
 * \brief Unit tests for symbol terms
 * \author Makai Mann
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <memory>
#include <string>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/utils.h"

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
    EXPECT_THROW(s->make_symbol("", boolsort), NotImplementedException);
    return;
  }
  Term empty = s->make_symbol("", boolsort);
  Term null_named = s->make_symbol("<null>", boolsort);
  EXPECT_EQ(empty->get_symbol_name(), "");
  EXPECT_EQ(null_named->get_symbol_name(), "<null>");
}

TEST_P(UnitSymbolTests, AtSignSymbolName)
{
  if (GetParam().solver_enum == MSAT)
  {
    EXPECT_THROW(s->make_symbol("@x", bvsort), NotImplementedException);
    return;
  }
  if (GetParam().solver_enum == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "The generic solver's binary may refuse names that "
                    "SMT-LIB reserves for the solver";
  }
  Term x = s->make_symbol("@x", bvsort);
  EXPECT_TRUE(x->is_symbolic_const());
  EXPECT_FALSE(x->is_value());
  EXPECT_EQ(x->get_symbol_name(), "@x");
}

TEST_P(UnitSymbolTests, InternalSymbolName)
{
  std::string name = internal_name("assump", 1);
  SolverEnum se = GetParam().solver_enum;
  if (se == BTOR || se == GENERIC_SOLVER || se == MSAT || se == Z3)
  {
    EXPECT_THROW(s->make_symbol(name, boolsort), IncorrectUsageException);
    return;
  }
  Term x = s->make_symbol(name, boolsort);
  EXPECT_EQ(x->get_symbol_name(), name);
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

TEST_P(UnitSymbolTests, SymbolHasNoConstructorOrSelectorName)
{
  Term x = s->make_symbol("x", bvsort);
  EXPECT_THROW(x->get_constructor_name(), IncorrectUsageException);
  EXPECT_THROW(x->get_selector_name(), IncorrectUsageException);
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
