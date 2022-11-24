/*********************                                                        */
/*! \file unit-term.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for terms.
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTermTests);
class UnitTermTests : public ::testing::Test,
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

TEST_P(UnitTermTests, FunOp)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  ASSERT_TRUE(x->is_symbol());
  ASSERT_TRUE(x->is_symbolic_const());
  ASSERT_TRUE(f->is_symbol());
  ASSERT_FALSE(f->is_symbolic_const());
}

TEST_P(UnitTermTests, Array)
{
  SolverConfiguration sc = GetParam();
  Term arr = s->make_symbol("arr", arrsort);
  ASSERT_TRUE(arr->is_symbol());
  ASSERT_TRUE(arr->is_symbolic_const());
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnitTerm,
                         UnitTermTests,
                         testing::ValuesIn(available_solver_configurations()));

}  // namespace smt_tests
