/*!
 * \file unit-arrays.cpp
 * \brief Unit tests for theory of arrays
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <string>
#include <unordered_set>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

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

  if (GetParam().solver_kind == SolverKind::YICES2)
  {
    // Yices2 has no model value for a constant array, which it keeps as a
    // lambda; the rest of this test asks for one
    return;
  }

  Term aval = s->get_value(a);
  EXPECT_EQ(aval->get_sort(), constarr0->get_sort());
  EXPECT_EQ(aval, constarr0);

  Term out_const_base;
  UnorderedTermMap assignments = s->get_array_values(a, out_const_base);
  EXPECT_TRUE(out_const_base);  // not null
  EXPECT_EQ(out_const_base, zero);
}

TEST_P(UnitArrayTests, StoreOfValuesIsValue)
{
  Term x = s->make_symbol("x", bvsort);
  Term zero = s->make_term(0, bvsort);
  Term one = s->make_term(1, bvsort);
  Term constarr0 = s->make_term(zero, arrsort);
  EXPECT_TRUE(s->make_term(Store, constarr0, zero, one)->is_value());
  EXPECT_FALSE(s->make_term(Store, constarr0, x, one)->is_value());
}

// two different entries, so that the value is not a constant array
TEST_P(UnitArrayTests, ValueHoldsTheAssertedEntries)
{
  Term a = s->make_symbol("a", arrsort);
  Term zero = s->make_term(0, bvsort);
  Term one = s->make_term(1, bvsort);
  s->assert_formula(s->make_term(Equal, s->make_term(Select, a, zero), one));
  s->assert_formula(s->make_term(Equal, s->make_term(Select, a, one), zero));
  ASSERT_TRUE(s->check_sat().is_sat());

  Term value = s->get_value(a);
  EXPECT_EQ(value->get_sort(), arrsort);
  EXPECT_TRUE(value->is_value()) << value;
  // the entry each store sets, the first store of an index winning, over
  // the constant array that holds every other index
  UnorderedTermMap entries;
  Term t = value;
  while (t->get_op() == Op(Store))
  {
    TermVec children(t->begin(), t->end());
    entries.emplace(children[1], children[2]);
    t = children[0];
  }
  ASSERT_NE(t->begin(), t->end()) << value;
  Term base = *t->begin();
  EXPECT_EQ(entries.count(zero) ? entries[zero] : base, one) << value;
  EXPECT_EQ(entries.count(one) ? entries[one] : base, zero) << value;
}

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitArray,
                         UnitArrayTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { CONSTARR, ARRAY_MODELS })));

}  // namespace
