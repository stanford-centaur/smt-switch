/*********************                                                        */
/*! \file test-term-translation.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for translating between solvers.
**
**
**/

#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"
#include "test-utils.h"

using namespace smt;
using namespace std;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SelfTranslationTests);
class SelfTranslationTests : public ::testing::Test,
                             public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    bvsort8 = s->make_sort(BV, 8);

    x = s->make_symbol("x", bvsort8);
    y = s->make_symbol("y", bvsort8);
    z = s->make_symbol("z", bvsort8);
  }
  SmtSolver s;
  Sort bvsort8;
  Term x, y, z;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SelfTranslationIntTests);
class SelfTranslationIntTests : public ::testing::Test,
                                public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    intsort = s->make_sort(INT);

    x = s->make_symbol("x", intsort);
    y = s->make_symbol("y", intsort);
    z = s->make_symbol("z", intsort);
  }
  SmtSolver s;
  Sort intsort;
  Term x, y, z;
};

class TranslationTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<tuple<SolverConfiguration, SolverConfiguration>>
{
 protected:
  void SetUp() override
  {
    s1 = create_solver(get<0>(GetParam()));
    s1->set_opt("produce-models", "true");

    s2 = create_solver(get<1>(GetParam()));
    s2->set_opt("produce-models", "true");

    boolsort = s1->make_sort(BOOL);
    bvsort8 = s1->make_sort(BV, 8);

    a = s1->make_symbol("a", boolsort);
    b = s1->make_symbol("b", boolsort);
    x = s1->make_symbol("x", bvsort8);
    y = s1->make_symbol("y", bvsort8);
    z = s1->make_symbol("z", bvsort8);
  }
  SmtSolver s1, s2;
  Sort boolsort, bvsort8;
  Term a, b, x, y, z;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(BoolArrayTranslationTests);
class BoolArrayTranslationTests : public TranslationTests
{
 protected:
  void SetUp() override
  {
    TranslationTests::SetUp();
    arrsort = s1->make_sort(ARRAY, bvsort8, boolsort);
    arr = s1->make_symbol("arr", arrsort);
  }
  Sort arrsort;
  Term arr;
};

TEST_P(SelfTranslationTests, BVTransfer)
{
  SmtSolver s2 = create_solver(GetParam());
  TermTranslator tt(s2);
  Term constraint = s->make_term(Equal, z, s->make_term(BVAdd, x, y));
  Term T = s->make_term(true);
  Term two = s->make_term(2, bvsort8);

  Term constraint2 = tt.transfer_term(constraint);
  Term T2 = tt.transfer_term(T);
  ASSERT_EQ(T2, s2->make_term(true));
  Term two_2 = tt.transfer_term(two);
  ASSERT_EQ(two_2, s2->make_term(2, s2->make_sort(BV, 8)));
  // ensure it can handle transfering again (even though it already built the
  // node)
  Term cached_constraint2 = constraint2;
  constraint2 = tt.transfer_term(constraint);
  ASSERT_EQ(cached_constraint2, constraint2);
  s2->assert_formula(constraint2);

  ASSERT_TRUE(s->check_sat().is_sat());
  ASSERT_TRUE(s2->check_sat().is_sat());
}

TEST_P(SelfTranslationIntTests, IntTransfer)
{
  SmtSolver s2 = create_solver(GetParam());
  TermTranslator tt(s2);

  Term xpy = s->make_term(Plus, x, y);
  Term xpymz = s->make_term(Minus, xpy, z);

  Term xpymz_transfer = tt.transfer_term(xpymz);
  // recover symbols
  unordered_map<string, Term> s2_symbols;
  for (auto sym : get_free_symbols(xpymz_transfer))
  {
    s2_symbols[sym->to_string()] = sym;
  }
  Term xpymz_2 =
      s2->make_term(Minus,
                    s2->make_term(Plus, s2_symbols.at("x"), s2_symbols.at("y")),
                    s2_symbols.at("z"));
  ASSERT_EQ(xpymz_transfer, xpymz_2);
  // test that you can retransfer
  xpymz_transfer = tt.transfer_term(xpymz);
  ASSERT_EQ(xpymz_transfer, xpymz_2);

  Term two = s->make_term(2, intsort);
  Term neg_two = s->make_term(Negate, two);
  Term xp2 = s->make_term(Plus, x, two);

  Term two_transfer = tt.transfer_term(two);
  Term two_2 = s2->make_term(2, intsort);
  ASSERT_EQ(two_transfer, two_2);

  Term neg_two_transfer = tt.transfer_term(neg_two);
  Term neg_two_2 = s2->make_term(Negate, two_2);
  ASSERT_EQ(neg_two_transfer, neg_two_2);

  Term xp2_transfer = tt.transfer_term(xp2);
  Term xp2_2 = s2->make_term(Plus, s2_symbols.at("x"), two_2);
  ASSERT_EQ(xp2_transfer, xp2_2);
}

TEST_P(TranslationTests, And)
{
  Term a_and_b = s1->make_term(And, a, b);
  TermTranslator to_s2(s2);

  TermTranslator to_s1(s1);

  Term a_and_b_2 = to_s2.transfer_term(a_and_b);
  Term a_and_b_1 = to_s1.transfer_term(a_and_b_2);
  ASSERT_EQ(a_and_b_1, a_and_b);
}

TEST_P(TranslationTests, Equal)
{
  Term a_equal_b = s1->make_term(Equal, a, b);
  TermTranslator to_s2(s2);

  TermTranslator to_s1(s1);

  Term a_equal_b_2 = to_s2.transfer_term(a_equal_b);
  // need to specify expected sortkind
  Term a_equal_b_1 = to_s1.transfer_term(a_equal_b_2, BOOL);

  // not guaranteed to be structurally equal -- might use different operators
  // or weird casting
  // but they should be semantically equivalent AND have the same sort
  // Note: boolector might still report that it's a BV1 instead of a Bool
  // but it will consistent
  ASSERT_EQ(a_equal_b->get_sort(), a_equal_b->get_sort());
  s1->assert_formula(s1->make_term(Distinct, a_equal_b_1, a_equal_b));
  Result r = s1->check_sat();
  ASSERT_TRUE(r.is_unsat());
}

TEST_P(TranslationTests, Ite)
{
  Term a_ite_x_y = s1->make_term(Ite, a, x, y);

  TermTranslator to_s2(s2);
  TermTranslator to_s1(s1);

  Term a_ite_x_y_2 = to_s2.transfer_term(a_ite_x_y);
  Term a_ite_x_y_1 = to_s1.transfer_term(a_ite_x_y_2);
  ASSERT_EQ(a_ite_x_y_1, a_ite_x_y);
}

TEST_P(TranslationTests, Concat)
{
  Sort bvsort1 = s1->make_sort(BV, 1);
  Term x_lt_y = s1->make_term(BVUlt, x, y);
  Term bv_x_lt_y = s1->make_term(
      Ite, x_lt_y, s1->make_term(1, bvsort1), s1->make_term(0, bvsort1));

  Term concat_term = s1->make_term(Concat, bv_x_lt_y, x);

  TermTranslator to_s2(s2);
  TermTranslator to_s1(s1);

  Term concat_term_2 = to_s2.transfer_term(concat_term);
  Term concat_term_1 = to_s1.transfer_term(concat_term_2);
  ASSERT_EQ(concat_term_1, concat_term);
}

TEST_P(TranslationTests, Extract)
{
  Sort bvsort1 = s1->make_sort(BV, 1);
  Term bv_a = s1->make_term(
      Ite, a, s1->make_term(1, bvsort1), s1->make_term(0, bvsort1));

  Term ext_bv_a = s1->make_term(Op(Extract, 0, 0), bv_a);

  TermTranslator to_s2(s2);
  TermTranslator to_s1(s1);

  Term ext_bv_a_2 = to_s2.transfer_term(ext_bv_a);
  // expect it to be a BV
  // ambiguous when working with BTOR because it's width 1
  Term ext_bv_a_1 = to_s1.transfer_term(ext_bv_a_2, BV);

  // this one might get rewritten
  // so it won't be syntactically equivalent
  // but it should still be semantically equivalent
  s1->assert_formula(s1->make_term(Distinct, ext_bv_a, ext_bv_a_1));
  Result r = s1->check_sat();
  ASSERT_TRUE(r.is_unsat());
}

TEST_P(TranslationTests, UninterpretedSort)
{
  Sort uninterp_sort;
  try
  {
    uninterp_sort = s1->make_sort("uninterp-sort", 0);
    // need to fail if either solver doesn't support uninterpreted sorts
    Sort dummy_sort = s2->make_sort("dummy", 0);
  }
  catch (SmtException & e)
  {
    // if this solver doesn't support uninterpreted sorts, that's fine
    // just stop the test
    return;
  }

  ASSERT_TRUE(uninterp_sort);
  Sort ufsort = s1->make_sort(FUNCTION, { uninterp_sort, boolsort });
  Term v = s1->make_symbol("v", uninterp_sort);
  Term f = s1->make_symbol("f", ufsort);
  Term fv = s1->make_term(Apply, f, v);

  TermTranslator to_s2(s2);
  TermTranslator to_s1(s1);

  Term fv_2 = to_s2.transfer_term(fv);
  EXPECT_EQ(fv_2->get_op(), Apply);

  Term fv_1 = to_s1.transfer_term(fv_2);
  EXPECT_EQ(fv, fv_1);
}

TEST_P(BoolArrayTranslationTests, Arrays)
{
  Term f = s1->make_term(false);
  Term t = s1->make_term(false);
  Term const_arr = s1->make_term(f, arrsort);
  Term stores = s1->make_term(Store, arr, x, t);
  stores = s1->make_term(Store, stores, y, t);

  TermTranslator to_s2(s2);
  TermTranslator to_s1(s1);

  Term stores_2 = to_s2.transfer_term(stores);
  Term stores_1 = to_s1.transfer_term(stores_2);
  ASSERT_EQ(stores, stores_1);
}

// All tests are instantiated with non-generic solver,
// as genreic solvers do not support term translation
// currently.

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSelfTranslationTests,
    SelfTranslationTests,
    testing::ValuesIn(filter_non_generic_solver_configurations({ TERMITER })));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSelfTranslationIntTests,
    SelfTranslationIntTests,
    testing::ValuesIn(filter_non_generic_solver_configurations(
        { FULL_TRANSFER, THEORY_INT })));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedTranslationTests,
    TranslationTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER })),
                     testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER }))));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedBoolArrayTranslationTests,
    BoolArrayTranslationTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, CONSTARR, ARRAY_FUN_BOOLS })),
                     testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, CONSTARR, ARRAY_FUN_BOOLS }))));

}  // namespace smt_tests
