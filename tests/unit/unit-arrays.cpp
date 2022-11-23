/*********************                                                        */
/*! \file unit-arrays.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for theory of arrays.
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitArrayTests);
class UnitArrayTests : public ::testing::Test,
                       public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  }
  SmtSolver s;
  Sort boolsort, bvsort, arrsort;
};

TEST_P(UnitArrayTests, ConstArr)
{
  Term x = s->make_symbol("x", bvsort);
  Term a = s->make_symbol("a", arrsort);
  Term zero = s->make_term(0, bvsort);
  Term constarr0 = s->make_term(zero, arrsort);
  EXPECT_TRUE(constarr0->get_op().is_null());
  EXPECT_FALSE(constarr0->is_symbol());
  EXPECT_TRUE(constarr0->is_value());
  // should have one child -- the value
  ASSERT_NE(constarr0->begin(), constarr0->end());
  Term val = *(constarr0->begin());
  EXPECT_EQ(val, zero);

  s->assert_formula(s->make_term(Equal, a, constarr0));
  Result r = s->check_sat();

  EXPECT_TRUE(r.is_sat());
  Term aval = s->get_value(a);
  EXPECT_EQ(aval->get_sort(), constarr0->get_sort());
  EXPECT_EQ(aval, constarr0);

  Term out_const_base;
  UnorderedTermMap assignments = s->get_array_values(a, out_const_base);
  EXPECT_TRUE(out_const_base);  // not null
  EXPECT_EQ(out_const_base, zero);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedUnitArray,
    UnitArrayTests,
    testing::ValuesIn(filter_solver_configurations({ CONSTARR, ARRAY_MODELS })));

}  // namespace smt_tests
