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
class ArrayModelTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    // distinct index and element sorts, so a check cannot mix them up
    idxsort = s->make_sort(BV, 4);
    elemsort = s->make_sort(BV, 8);
    arrsort = s->make_sort(ARRAY, idxsort, elemsort);
    arr = s->make_symbol("arr", arrsort);
    i = s->make_symbol("i", idxsort);
    j = s->make_symbol("j", idxsort);
    one = s->make_term(1, elemsort);
    two = s->make_term(2, elemsort);
  }
  SmtSolver s;
  Sort idxsort, elemsort, arrsort;
  Term arr, i, j, one, two;
};

/* What the model says an array holds at one index: the entry the solver
 * listed, or the constant base standing in for every index it did not.
 */
static Term model_value_at(const UnorderedTermMap & array_vals,
                           const Term & const_base,
                           const Term & idx)
{
  auto entry = array_vals.find(idx);
  return entry == array_vals.end() ? const_base : entry->second;
}

TEST_P(ArrayModelTests, TestArrayModel)
{
  Term constraint1 = s->make_term(Equal, s->make_term(Select, arr, i), one);
  Term constraint2 = s->make_term(Equal, s->make_term(Select, arr, j), two);
  s->assert_formula(s->make_term(And, constraint1, constraint2));
  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  Term const_base;
  UnorderedTermMap array_vals = s->get_array_values(arr, const_base);

  if (const_base)
  {
    // if the solver provided a const array base
    // check that it has the element sort
    EXPECT_EQ(const_base->get_sort(), arr->get_sort()->get_elemsort());
  }

  // How many stores a solver needs is its own business -- one that picks a
  // constant base equal to a required value lists one index where another
  // lists two. So check what the model means rather than its size: every
  // index it does list must read back the same, and the two constrained
  // indices must hold what was asserted, listed or left to the base.
  for (const auto & entry : array_vals)
  {
    EXPECT_EQ(s->get_value(s->make_term(Select, arr, entry.first)),
              entry.second);
  }

  Term iv = s->get_value(i);
  Term jv = s->get_value(j);
  ASSERT_NE(iv, jv);
  EXPECT_EQ(model_value_at(array_vals, const_base, iv), one);
  EXPECT_EQ(model_value_at(array_vals, const_base, jv), two);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedArrayModelTests,
    ArrayModelTests,
    testing::ValuesIn(filter_solver_configurations({ ARRAY_MODELS })));

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ArrayTests);
class ArrayTests : public ::testing::Test,
                   public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override { s = create_solver(GetParam()); }
  SmtSolver s;
};

TEST_P(ArrayTests, EqualIndicesEqualReads)
{
  Sort bvsort32 = s->make_sort(BV, 32);
  Sort array32_32 = s->make_sort(ARRAY, bvsort32, bvsort32);
  Term x = s->make_symbol("x", bvsort32);
  Term y = s->make_symbol("y", bvsort32);
  Term arr = s->make_symbol("arr", array32_32);

  s->assert_formula(
      s->make_term(Not,
                   s->make_term(Implies,
                                s->make_term(Equal, x, y),
                                s->make_term(Equal,
                                             s->make_term(Select, arr, x),
                                             s->make_term(Select, arr, y)))));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

INSTANTIATE_TEST_SUITE_P(,
                         ArrayTests,
                         testing::ValuesIn(available_solver_configurations()),
                         ConfigName());

}  // namespace smt_tests
