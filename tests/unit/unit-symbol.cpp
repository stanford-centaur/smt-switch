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

#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

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

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnitSymbol,
                         UnitSymbolTests,
                         testing::ValuesIn(available_solver_configurations()));

}  // namespace smt_tests
