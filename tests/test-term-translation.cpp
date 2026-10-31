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

#include <gtest/gtest.h>

#include <cstddef>
#include <memory>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "available_solvers.h"
#include "datatype.h"
#include "exceptions.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"
#include "term_translator.h"
#include "term_utils.h"
#include "utils.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SelfTranslationTests);
class SelfTranslationTests
    : public testing::Test,
      public testing::WithParamInterface<SolverConfiguration>
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
class SelfTranslationIntTests
    : public testing::Test,
      public testing::WithParamInterface<SolverConfiguration>
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SelfTranslationRealTests);
class SelfTranslationRealTests
    : public testing::Test,
      public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    realsort = s->make_sort(REAL);

    x = s->make_symbol("x", realsort);
    y = s->make_symbol("y", realsort);
  }
  SmtSolver s;
  Sort realsort;
  Term x, y;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(TranslationTests);
class TranslationTests : public testing::Test,
                         public testing::WithParamInterface<
                             tuple<SolverConfiguration, SolverConfiguration>>
{
 protected:
  void SetUp() override
  {
    s1 = create_solver(get<0>(GetParam()));
    s1->set_opt("produce-models", "true");

    s2 = create_solver(get<1>(GetParam()));
    s2->set_opt("produce-models", "true");

    boolsort = s1->make_sort(BOOL);

    a = s1->make_symbol("a", boolsort);
    b = s1->make_symbol("b", boolsort);
  }
  SmtSolver s1, s2;
  Sort boolsort;
  Term a, b;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(BVTranslationTests);
class BVTranslationTests : public TranslationTests
{
 protected:
  void SetUp() override
  {
    TranslationTests::SetUp();
    bvsort8 = s1->make_sort(BV, 8);

    x = s1->make_symbol("x", bvsort8);
    y = s1->make_symbol("y", bvsort8);
    z = s1->make_symbol("z", bvsort8);
  }
  Sort bvsort8;
  Term x, y, z;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(BoolArrayTranslationTests);
class BoolArrayTranslationTests : public BVTranslationTests
{
 protected:
  void SetUp() override
  {
    BVTranslationTests::SetUp();
    arrsort = s1->make_sort(ARRAY, bvsort8, boolsort);
    arr = s1->make_symbol("arr", arrsort);
  }
  Sort arrsort;
  Term arr;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(StringTranslationTests);
class StringTranslationTests : public TranslationTests
{
 protected:
  void SetUp() override
  {
    TranslationTests::SetUp();
    strsort = s1->make_sort(STRING);
  }
  Sort strsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IntTranslationTests);
class IntTranslationTests : public TranslationTests
{
 protected:
  void SetUp() override
  {
    TranslationTests::SetUp();
    intsort = s1->make_sort(INT);
    i = s1->make_symbol("i", intsort);
    j = s1->make_symbol("j", intsort);
    k = s1->make_symbol("k", intsort);
  }
  Sort intsort;
  Term i, j, k;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(RealTranslationTests);
class RealTranslationTests : public TranslationTests
{
 protected:
  void SetUp() override
  {
    TranslationTests::SetUp();
    realsort = s1->make_sort(REAL);
  }
  Sort realsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IntRealTranslationTests);
class IntRealTranslationTests : public RealTranslationTests
{
 protected:
  void SetUp() override
  {
    RealTranslationTests::SetUp();
    intsort = s1->make_sort(INT);
  }
  Sort intsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(DatatypeTranslationTests);
class DatatypeTranslationTests : public TranslationTests
{
 protected:
  void SetUp() override
  {
    TranslationTests::SetUp();
    intsort = s1->make_sort(INT);
    DatatypeDecl listdecl = s1->make_datatype_decl("list");
    DatatypeConstructorDecl nildecl = s1->make_datatype_constructor_decl("nil");
    DatatypeConstructorDecl consdecl =
        s1->make_datatype_constructor_decl("cons");
    s1->add_selector(consdecl, "head", intsort);
    s1->add_selector_self(consdecl, "tail");
    s1->add_constructor(listdecl, nildecl);
    s1->add_constructor(listdecl, consdecl);
    listsort = s1->make_sort(listdecl);
  }
  Sort intsort, listsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SortConstructorTranslationTests);
class SortConstructorTranslationTests : public TranslationTests
{
 protected:
  void SetUp() override
  {
    TranslationTests::SetUp();
    list = s1->make_sort("List", 1);
    list_bool = s1->make_sort(list, SortVec{ boolsort });
  }
  Sort list, list_bool;
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
  // ensure it can handle transferring again (even though it already built the
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
  UnorderedTermSet free_symbols;
  get_free_symbolic_consts(xpymz_transfer, free_symbols);
  unordered_map<string, Term> s2_symbols;
  for (auto sym : free_symbols)
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

TEST_P(SelfTranslationIntTests, Abs)
{
  SmtSolver s2 = create_solver(GetParam());
  TermTranslator tt(s2);

  Term abs_x_transfer = tt.transfer_term(s->make_term(Abs, x));
  Term abs_x_2 = s2->make_term(Abs, s2->get_symbol("x"));
  s2->assert_formula(s2->make_term(Distinct, abs_x_transfer, abs_x_2));
  ASSERT_TRUE(s2->check_sat().is_unsat());
}

TEST_P(SelfTranslationRealTests, Fractions)
{
  SmtSolver s2 = create_solver(GetParam());
  TermTranslator tt(s2);

  Term half = s->make_term("1/2", realsort);
  Term neg_half = s->make_term("-1/2", realsort);
  Term constraint =
      s->make_term(And,
                   s->make_term(Equal, s->make_term(Plus, x, y), half),
                   s->make_term(Lt, x, neg_half));

  Term half_transfer = tt.transfer_term(half);
  Term neg_half_transfer = tt.transfer_term(neg_half);
  Term constraint_transfer = tt.transfer_term(constraint);
  EXPECT_EQ(half_transfer->get_sort()->get_sort_kind(), REAL);
  EXPECT_EQ(neg_half_transfer->get_sort()->get_sort_kind(), REAL);

  Sort realsort2 = s2->make_sort(REAL);
  Term half_2 = s2->make_term("1/2", realsort2);
  Term neg_half_2 = s2->make_term("-1/2", realsort2);
  Term constraint_2 = s2->make_term(
      And,
      s2->make_term(
          Equal,
          s2->make_term(Plus, s2->get_symbol("x"), s2->get_symbol("y")),
          half_2),
      s2->make_term(Lt, s2->get_symbol("x"), neg_half_2));

  s2->assert_formula(s2->make_term(
      Or,
      s2->make_term(Distinct, half_transfer, half_2),
      s2->make_term(Distinct, neg_half_transfer, neg_half_2),
      s2->make_term(Distinct, constraint_transfer, constraint_2)));
  EXPECT_TRUE(s2->check_sat().is_unsat());

  s->assert_formula(constraint);
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST_P(TranslationTests, And)
{
  Term a_and_b = s1->make_term(And, a, b);
  TermTranslator to_s2(s2);

  TermTranslator to_s1(s1);

  Term a_and_b_2 = to_s2.transfer_term(a_and_b);
  Term a_and_b_1 = to_s1.transfer_term(a_and_b_2);
  ASSERT_TRUE(round_trip_matches(get<1>(GetParam()), s1, a_and_b_1, a_and_b));
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

TEST_P(BVTranslationTests, NaryApplications)
{
  // a source solver may keep these as applications to three arguments, of
  // which a target solver may only take two at a time
  TermVec bool_terms({ s1->make_term(Implies, { a, b, a }),
                       s1->make_term(Equal, { x, y, z }),
                       s1->make_term(Distinct, { x, y, z }) });
  Term product = s1->make_term(BVMul, { x, y, z });
  TermTranslator to_s2(s2);
  TermTranslator to_s1(s1);

  TermVec differences;
  for (const Term & t : bool_terms)
  {
    Term t_1 = to_s1.transfer_term(to_s2.transfer_term(t), BOOL);
    differences.push_back(s1->make_term(Distinct, t, t_1));
  }
  Term product_1 = to_s1.transfer_term(to_s2.transfer_term(product), BV);
  differences.push_back(s1->make_term(Distinct, product, product_1));
  s1->assert_formula(s1->make_term(Or, differences));
  ASSERT_TRUE(s1->check_sat().is_unsat());
}

TEST_P(IntTranslationTests, NaryApplications)
{
  // a source solver may keep these as applications to three arguments, as
  // Yices2 keeps a sum
  Term sum = s1->make_term(Plus, { i, j, k });
  Term difference = s1->make_term(Minus, { i, j, k });
  Term chain = s1->make_term(Lt, { i, j, k });
  TermTranslator to_s2(s2);
  TermTranslator to_s1(s1);

  TermVec differences;
  for (const Term & t : { sum, difference })
  {
    Term t_1 = to_s1.transfer_term(to_s2.transfer_term(t), INT);
    differences.push_back(s1->make_term(Distinct, t, t_1));
  }
  Term chain_1 = to_s1.transfer_term(to_s2.transfer_term(chain), BOOL);
  differences.push_back(s1->make_term(Distinct, chain, chain_1));
  s1->assert_formula(s1->make_term(Or, differences));
  ASSERT_TRUE(s1->check_sat().is_unsat());
}

TEST_P(BVTranslationTests, Ite)
{
  Term a_ite_x_y = s1->make_term(Ite, a, x, y);

  TermTranslator to_s2(s2);
  TermTranslator to_s1(s1);

  Term a_ite_x_y_2 = to_s2.transfer_term(a_ite_x_y);
  Term a_ite_x_y_1 = to_s1.transfer_term(a_ite_x_y_2);
  ASSERT_TRUE(
      round_trip_matches(get<1>(GetParam()), s1, a_ite_x_y_1, a_ite_x_y));
}

TEST_P(BVTranslationTests, Concat)
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
  ASSERT_TRUE(
      round_trip_matches(get<1>(GetParam()), s1, concat_term_1, concat_term));
}

TEST_P(BVTranslationTests, Extract)
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
  EXPECT_TRUE(round_trip_matches(get<1>(GetParam()), s1, fv_1, fv));
}

TEST_P(BoolArrayTranslationTests, Arrays)
{
  if (get<0>(GetParam()).solver_enum == YICES2
      || get<1>(GetParam()).solver_enum == YICES2)
  {
    GTEST_SKIP() << "Yices2 cannot read an array constrained to equal a "
                    "constant array";
  }

  Term f = s1->make_term(false);
  Term t = s1->make_term(true);
  Term const_arr = s1->make_term(f, arrsort);
  Term stores = s1->make_term(Store, const_arr, x, t);
  stores = s1->make_term(Store, stores, y, t);

  TermTranslator to_s2(s2);
  TermTranslator to_s1(s1);

  Term const_arr_2 = to_s2.transfer_term(const_arr);
  EXPECT_EQ(const_arr_2->get_sort(),
            s2->make_sort(ARRAY, s2->make_sort(BV, 8), s2->make_sort(BOOL)));
  EXPECT_TRUE(const_arr_2->is_value());
  EXPECT_EQ(to_s1.transfer_term(const_arr_2), const_arr);

  Term stores_2 = to_s2.transfer_term(stores);
  Term stores_1 = to_s1.transfer_term(stores_2);
  EXPECT_EQ(stores, stores_1);

  // stores is false everywhere except at x and y
  Term constraint = s1->make_term(And,
                                  { s1->make_term(Equal, arr, stores),
                                    s1->make_term(Distinct, z, x),
                                    s1->make_term(Distinct, z, y),
                                    s1->make_term(Select, arr, z) });
  s1->assert_formula(constraint);
  EXPECT_TRUE(s1->check_sat().is_unsat());
  s2->assert_formula(to_s2.transfer_term(constraint));
  EXPECT_TRUE(s2->check_sat().is_unsat());
}

TEST_P(RealTranslationTests, IteOverIntegerValuedReal)
{
  // MathSAT and Yices2 make 0.0, 1.0 and an Ite over them Ints, and 1/10 a
  // Real, so these Ites have one branch of each
  auto make_ites = [](const SmtSolver & solver,
                      const Term & c,
                      const Term & d) {
    Sort real = solver->make_sort(REAL);
    Term zero = solver->make_term("0.0", real);
    Term one = solver->make_term("1.0", real);
    Term tenth = solver->make_term("1/10", real);
    return TermVec{ solver->make_term(Ite, c, zero, tenth),
                    solver->make_term(Ite, c, tenth, zero),
                    solver->make_term(
                        Ite, c, solver->make_term(Ite, d, zero, one), tenth) };
  };
  TermVec ites = make_ites(s1, a, b);
  Sort boolsort2 = s2->make_sort(BOOL);
  TermVec expected = make_ites(
      s2, s2->make_symbol("a", boolsort2), s2->make_symbol("b", boolsort2));

  TermTranslator to_s2(s2);
  TermVec distinct;
  for (size_t n = 0; n < ites.size(); ++n)
  {
    SCOPED_TRACE(ites[n]->to_string());
    Term ite2 = to_s2.transfer_term(ites[n]);
    EXPECT_EQ(ite2->get_sort()->get_sort_kind(), REAL);
    distinct.push_back(s2->make_term(Distinct, ite2, expected[n]));
  }
  s2->assert_formula(s2->make_term(Or, distinct));
  EXPECT_TRUE(s2->check_sat().is_unsat());
}

TEST_P(RealTranslationTests, EqualOverIntegerValuedReal)
{
  // MathSAT and Yices2 make 1.0 an Int, so this = and this distinct over
  // Reals have an Int side
  Term x = s1->make_symbol("x", realsort);
  Term one = s1->make_term("1.0", realsort);
  TermTranslator to_s2(s2);
  s2->assert_formula(to_s2.transfer_term(s1->make_term(Equal, x, one)));
  s2->assert_formula(to_s2.transfer_term(s1->make_term(Distinct, one, x)));
  EXPECT_TRUE(s2->check_sat().is_unsat());
}

TEST_P(IntRealTranslationTests, Conversions)
{
  // x is i + 1/2, so i is the integer part of x
  Term i = s1->make_symbol("i", intsort);
  Term x = s1->make_symbol("x", realsort);
  Term half = s1->make_term(
      Div, s1->make_term(1, realsort), s1->make_term(2, realsort));
  Term constraint = s1->make_term(
      And,
      s1->make_term(
          Equal, x, s1->make_term(Plus, s1->make_term(To_Real, i), half)),
      s1->make_term(Distinct, s1->make_term(To_Int, x), i));

  TermTranslator to_s2(s2);
  s2->assert_formula(to_s2.transfer_term(constraint));
  EXPECT_TRUE(s2->check_sat().is_unsat());
}

TEST_P(StringTranslationTests, Strings)
{
  Term t = s1->make_term("\\u{a}-\"foo\"", true, strsort);
  Term nt = s1->make_term("", false, strsort);

  TermTranslator to_s2(s2);
  TermTranslator to_s1(s1);

  Term t2 = to_s2.transfer_term(t);
  EXPECT_EQ(t2->to_string(), t->to_string());
  Term nt2 = to_s2.transfer_term(nt);
  EXPECT_EQ(nt2->to_string(), nt->to_string());

  Term t1 = to_s1.transfer_term(t2);
  EXPECT_EQ(t, t1);
  Term nt1 = to_s1.transfer_term(nt2);
  EXPECT_EQ(nt, nt1);
}

TEST_P(DatatypeTranslationTests, DatatypeSort)
{
  TermTranslator to_s2(s2);
  Sort list2 = to_s2.transfer_sort(listsort);
  ASSERT_EQ(list2->get_sort_kind(), DATATYPE);
  // declared once, so every transfer gives the same datatype
  EXPECT_EQ(to_s2.transfer_sort(listsort), list2);

  Datatype dt2 = list2->get_datatype();
  EXPECT_EQ(dt2->get_name(), "list");
  EXPECT_EQ(dt2->get_constructor_names(), (vector<string>{ "nil", "cons" }));
  EXPECT_EQ(dt2->get_selector_names("cons"),
            (vector<string>{ "head", "tail" }));
  EXPECT_EQ(dt2->get_selector_sort("cons", "head"), s2->make_sort(INT));
  EXPECT_EQ(dt2->get_selector_sort("cons", "tail"), list2);

  // a symbol of the datatype transfers with it, and s2 can reason about it
  Term l2 = to_s2.transfer_term(s1->make_symbol("l", listsort));
  EXPECT_EQ(l2->get_sort(), list2);
  s2->assert_formula(
      s2->make_term(Apply_Tester, s2->get_tester(list2, "cons"), l2));
  s2->assert_formula(s2->make_term(
      Apply_Tester,
      s2->get_tester(list2, "nil"),
      s2->make_term(
          Apply_Selector, s2->get_selector(list2, "cons", "tail"), l2)));
  EXPECT_TRUE(s2->check_sat().is_sat());
}

TEST_P(DatatypeTranslationTests, NestedDatatype)
{
  // a datatype with a selector of another datatype brings that one along
  DatatypeDecl pairdecl = s1->make_datatype_decl("pair");
  DatatypeConstructorDecl mkpair = s1->make_datatype_constructor_decl("mkpair");
  s1->add_selector(mkpair, "first", listsort);
  s1->add_selector(mkpair, "second", listsort);
  s1->add_constructor(pairdecl, mkpair);
  Sort pairsort = s1->make_sort(pairdecl);

  TermTranslator to_s2(s2);
  Sort pair2 = to_s2.transfer_sort(pairsort);
  Datatype dt2 = pair2->get_datatype();
  Sort list2 = dt2->get_selector_sort("mkpair", "first");
  EXPECT_EQ(list2->get_datatype()->get_name(), "list");
  // both selectors share the one transferred list
  EXPECT_EQ(dt2->get_selector_sort("mkpair", "second"), list2);
  EXPECT_EQ(to_s2.transfer_sort(listsort), list2);
}

TEST_P(SortConstructorTranslationTests, SortConstructor)
{
  TermTranslator to_s2(s2);
  Sort list2 = to_s2.transfer_sort(list);
  EXPECT_EQ(list2->get_sort_kind(), UNINTERPRETED_CONS);
  EXPECT_EQ(list2->get_uninterpreted_name(), "List");
  EXPECT_EQ(list2->get_arity(), 1);
}

TEST_P(SortConstructorTranslationTests, AppliedSorts)
{
  // (List (List Bool)) nests one application of the constructor in another
  Sort list_list_bool = s1->make_sort(list, SortVec{ list_bool });
  Term l = s1->make_symbol("l", list_bool);
  Term ll = s1->make_symbol("ll", list_list_bool);
  Term f = s1->make_symbol(
      "f", s1->make_sort(FUNCTION, SortVec{ list_list_bool, list_bool }));
  Term eq = s1->make_term(Equal, s1->make_term(Apply, f, ll), l);

  // applying f in s2 is well sorted only if both applied sorts share one
  // constructor there
  TermTranslator to_s2(s2);
  Term eq2 = to_s2.transfer_term(eq);
  Sort list_bool2 = to_s2.transfer_term(l)->get_sort();
  EXPECT_EQ(list_bool2->get_sort_kind(), UNINTERPRETED);
  EXPECT_EQ(list_bool2->get_uninterpreted_name(), "List");
  SortVec params = list_bool2->get_uninterpreted_param_sorts();
  ASSERT_EQ(params.size(), 1);
  EXPECT_EQ(params[0]->get_sort_kind(), BOOL);
  EXPECT_EQ(to_s2.transfer_sort(list_list_bool),
            to_s2.transfer_term(ll)->get_sort());

  s2->assert_formula(eq2);
  EXPECT_TRUE(s2->check_sat().is_sat());
}

TEST_P(SortConstructorTranslationTests, ArityClash)
{
  // a nullary sort with a constructor's name cannot share its declaration
  Sort list0 = s1->make_sort("List", 0);
  TermTranslator to_s2(s2);
  to_s2.transfer_sort(list);
  EXPECT_THROW(to_s2.transfer_sort(list0), IncorrectUsageException);
}

// All tests are instantiated with non-generic solvers,
// as generic solvers do not support term translation
// currently.

INSTANTIATE_TEST_SUITE_P(
    ,
    SelfTranslationTests,
    testing::ValuesIn(filter_non_generic_solver_configurations({ TERMITER })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ,
    SelfTranslationIntTests,
    testing::ValuesIn(filter_non_generic_solver_configurations({ FULL_TRANSFER,
                                                                 THEORY_INT })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ,
    SelfTranslationRealTests,
    testing::ValuesIn(filter_non_generic_solver_configurations(
        { FULL_TRANSFER, THEORY_REAL })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ,
    TranslationTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER })),
                     testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER }))),
    ConfigPairName());

INSTANTIATE_TEST_SUITE_P(
    ,
    BVTranslationTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, THEORY_BV })),
                     testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, THEORY_BV }))),
    ConfigPairName());

INSTANTIATE_TEST_SUITE_P(
    ,
    BoolArrayTranslationTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, CONSTARR, ARRAY_FUN_BOOLS })),
                     testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, CONSTARR, ARRAY_FUN_BOOLS }))),
    ConfigPairName());

INSTANTIATE_TEST_SUITE_P(
    ,
    IntTranslationTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, THEORY_INT })),
                     testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, THEORY_INT }))),
    ConfigPairName());

INSTANTIATE_TEST_SUITE_P(
    ,
    RealTranslationTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, THEORY_REAL })),
                     testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, THEORY_REAL }))),
    ConfigPairName());

INSTANTIATE_TEST_SUITE_P(
    ,
    IntRealTranslationTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, THEORY_INT, THEORY_REAL })),
                     testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, THEORY_INT, THEORY_REAL }))),
    ConfigPairName());

INSTANTIATE_TEST_SUITE_P(
    ,
    StringTranslationTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, THEORY_STR })),
                     testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, THEORY_STR }))),
    ConfigPairName());

INSTANTIATE_TEST_SUITE_P(
    ,
    DatatypeTranslationTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, THEORY_DATATYPE })),
                     testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, THEORY_DATATYPE }))),
    ConfigPairName());

INSTANTIATE_TEST_SUITE_P(
    ,
    SortConstructorTranslationTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, PARAM_UNINTERP_SORT })),
                     testing::ValuesIn(filter_non_generic_solver_configurations(
                         { TERMITER, PARAM_UNINTERP_SORT }))),
    ConfigPairName());

}  // namespace
