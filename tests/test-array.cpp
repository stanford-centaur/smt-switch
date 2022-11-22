/*********************                                                        */
/*! \file test-array.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for theory of arrays.
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ArrayModelTests);
class ArrayModelTests : public ::testing::Test,
                        public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    bvsort = s->make_sort(BV, 8);
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
    arr = s->make_symbol("arr", arrsort);
    i = s->make_symbol("i", bvsort);
    j = s->make_symbol("j", bvsort);
    one = s->make_term(1, bvsort);
    two = s->make_term(2, bvsort);
  }
  SmtSolver s;
  Sort bvsort, arrsort;
  Term arr, i, j, one, two;
};

TEST_P(ArrayModelTests, TestArrayModel)
{
  Term constraint1 = s->make_term(Equal, s->make_term(Select, arr, i), one);
  Term constraint2 = s->make_term(Equal, s->make_term(Select, arr, j), two);
  s->assert_formula(s->make_term(And, constraint1, constraint2));
  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  Term const_base;
  UnorderedTermMap array_vals = s->get_array_values(arr, const_base);
  Term iv = s->get_value(i);
  Term jv = s->get_value(j);
  Term arriv = s->get_value(s->make_term(Select, arr, iv));
  Term arrjv = s->get_value(s->make_term(Select, arr, jv));
  // expecting only two relevant indices
  ASSERT_EQ(array_vals.size(), 2);
  ASSERT_EQ(arriv, array_vals[iv]);
  ASSERT_EQ(arrjv, array_vals[jv]);

  if (const_base)
  {
    // if the solver provided a const array base
    // check that the sort matches
    ASSERT_EQ(const_base->get_sort(), arr->get_sort()->get_indexsort());
  }
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedArrayModelTests,
    ArrayModelTests,
    testing::ValuesIn(filter_solver_configurations({ ARRAY_MODELS })));

}  // namespace smt_tests
