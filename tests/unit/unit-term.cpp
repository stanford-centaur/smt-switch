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

#include <cstdint>
#include <functional>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>

#include "available_solvers.h"
#include "exceptions.h"
#include "gtest/gtest.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTermTests);
class UnitTermTests : public ::testing::Test,
                      public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  }
  SmtSolver s;
  Sort boolsort, bvsort, funsort, arrsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTermArithTests);
class UnitTermArithTests : public UnitTermTests
{
 protected:
  void SetUp() override
  {
    UnitTermTests::SetUp();
    intsort = s->make_sort(INT);
    realsort = s->make_sort(REAL);
  }
  Sort intsort, realsort;
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

  EXPECT_EQ(fx->get_op(), Apply);
  ASSERT_NE(fx->begin(), fx->end());
  EXPECT_EQ(*fx->begin(), f);
  EXPECT_EQ(fx->get_sort(), bvsort);
}

TEST_P(UnitTermTests, MultiArgFunOp)
{
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort8);
  Term g = s->make_symbol(
      "g", s->make_sort(FUNCTION, SortVec{ bvsort, bvsort8, bvsort8 }));
  Term h = s->make_symbol(
      "h",
      s->make_sort(FUNCTION, SortVec{ bvsort, bvsort8, bvsort, boolsort }));

  Term gxy = s->make_term(Apply, g, x, y);
  EXPECT_EQ(gxy->get_op(), Apply);
  EXPECT_EQ(gxy->get_sort(), bvsort8);
  Term hxyx = s->make_term(Apply, TermVec{ h, x, y, x });
  EXPECT_EQ(hxyx->get_op(), Apply);
  EXPECT_EQ(hxyx->get_sort(), boolsort);
}

TEST_P(UnitTermTests, BoolValues)
{
  Term t = s->make_term(true);
  Term f = s->make_term(false);
  EXPECT_TRUE(t->is_value());
  EXPECT_TRUE(f->is_value());
  EXPECT_NE(t, f);
  EXPECT_EQ(t->get_sort(), boolsort);
  EXPECT_EQ(f->get_sort(), boolsort);
}

TEST_P(UnitTermTests, TermShorthands)
{
  Term a = s->make_symbol("a", boolsort);
  Term b = s->make_symbol("b", boolsort);
  Term c = s->make_symbol("c", boolsort);
  Term d = s->make_symbol("d", boolsort);
  EXPECT_EQ(s->make_term(Not, a), s->make_term(Not, TermVec{ a }));
  EXPECT_EQ(s->make_term(Xor, a, b), s->make_term(Xor, TermVec{ a, b }));
  EXPECT_EQ(s->make_term(Ite, a, b, c), s->make_term(Ite, TermVec{ a, b, c }));
  EXPECT_EQ(s->make_term(And, a, b, c, d),
            s->make_term(And, TermVec{ a, b, c, d }));
}

TEST_P(UnitTermTests, BVSorts)
{
  EXPECT_EQ(s->make_term(5, bvsort)->get_sort(), bvsort);
  Term x = s->make_symbol("x", bvsort);
  EXPECT_EQ(s->make_term(Concat, x, x)->get_sort(), s->make_sort(BV, 8));
  EXPECT_EQ(s->make_term(Op(Extract, 2, 1), x)->get_sort(),
            s->make_sort(BV, 2));
  EXPECT_EQ(s->make_term(Op(Zero_Extend, 1), x)->get_sort(),
            s->make_sort(BV, 5));
}

TEST_P(UnitTermTests, Array)
{
  Term arr = s->make_symbol("arr", arrsort);
  ASSERT_TRUE(arr->is_symbol());
  ASSERT_TRUE(arr->is_symbolic_const());
}

TEST_P(UnitTermTests, SymbolSurvivesSubstitution)
{
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term a = s->make_symbol("a", bvsort);
  Term b = s->make_symbol("b", bvsort);
  Term arr = s->make_symbol("arr", arrsort);
  Term arr2 = s->make_symbol("arr2", arrsort);
  s->assert_formula(s->make_term(Equal, x, s->make_term(BVAdd, a, b)));
  s->assert_formula(s->make_term(Equal, y, s->make_term(5, bvsort)));
  s->assert_formula(s->make_term(Equal, arr, arr2));
  ASSERT_TRUE(s->check_sat().is_sat());

  for (const Term & t : { x, y, arr })
  {
    EXPECT_TRUE(t->is_symbol()) << t;
    EXPECT_TRUE(t->is_symbolic_const()) << t;
    EXPECT_FALSE(t->is_value()) << t;
    EXPECT_TRUE(t->get_op().is_null()) << t;
    EXPECT_EQ(t->begin(), t->end()) << t;
    // iterating must not change the answers
    EXPECT_TRUE(t->is_symbol()) << t;
    EXPECT_FALSE(t->is_value()) << t;
  }
}

TEST_P(UnitTermTests, TermContainers)
{
  const size_t num_terms = 20;
  Sort bvsort8 = s->make_sort(BV, 8);

  UnorderedTermSet uts;
  UnorderedTermMap utm;
  TermVec v;
  v.reserve(num_terms);
  for (size_t i = 0; i < num_terms; ++i)
  {
    Term x = s->make_symbol("x" + to_string(i), bvsort8);
    Term y = s->make_symbol("y" + to_string(i), bvsort8);
    v.push_back(x);
    uts.insert(x);
    utm[x] = y;
  }
  EXPECT_EQ(uts.size(), num_terms);
  EXPECT_EQ(utm.size(), num_terms);

  Term one = s->make_term(1, bvsort8);
  for (size_t i = 1; i < num_terms; ++i)
  {
    s->assert_formula(
        s->make_term(Equal, v[i], s->make_term(BVAdd, v[i - 1], one)));
  }

  Term zero = s->make_term(0, bvsort8);
  EXPECT_TRUE(zero->is_value());
  EXPECT_FALSE(v[0]->is_value());
  EXPECT_TRUE(v[0]->is_symbolic_const());
  s->assert_formula(s->make_term(Equal, v[0], zero));

  for (const Term & x : uts)
  {
    s->assert_formula(s->make_term(Equal, x, utm.at(x)));
  }

  ASSERT_TRUE(s->check_sat().is_sat());

  // v[0] = 0 and each v[i] = v[i-1] + 1, so v[i] = i; each y equals its x
  for (size_t i = 0; i < num_terms; ++i)
  {
    EXPECT_EQ(s->get_value(v[i])->to_int(), i);
    EXPECT_EQ(s->get_value(utm.at(v[i]))->to_int(), i);
  }
}

TEST(NullTerm, EquivalentToNullTerm)
{
  Term t1, t2;
  EXPECT_EQ(t1, t2);
  EXPECT_FALSE(t1 != t2);
  EXPECT_FALSE(t1 < t2);
  EXPECT_FALSE(t1 > t2);
  EXPECT_LE(t1, t2);
  EXPECT_GE(t1, t2);
}

TEST(NullTerm, HashesToZero) { EXPECT_EQ(std::hash<Term>{}(Term()), 0u); }

TEST(NullTerm, PrintsNull)
{
  std::ostringstream out;
  out << Term();
  EXPECT_EQ(out.str(), "null");
}

TEST(NullTerm, CannotBeIterated)
{
  Term t;
  EXPECT_THROW(smt::begin(t), IncorrectUsageException);
  EXPECT_THROW(smt::end(t), IncorrectUsageException);
}

TEST_P(UnitTermTests, NullTermSortsBeforeTerm)
{
  Term x = s->make_symbol("x", bvsort);
  Term null;
  EXPECT_NE(x, null);
  EXPECT_NE(null, x);
  EXPECT_LT(null, x);
  EXPECT_LE(null, x);
  EXPECT_GT(x, null);
  EXPECT_GE(x, null);
  EXPECT_FALSE(x < null);
  EXPECT_FALSE(null > x);
}

TEST_P(UnitTermTests, NullTermInSet)
{
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  UnorderedTermSet uts{ x, Term(), y, Term() };
  EXPECT_EQ(uts.size(), 3u);
  EXPECT_EQ(uts.count(Term()), 1u);
}

TEST_P(UnitTermArithTests, Sorts)
{
  EXPECT_EQ(s->make_term(1, intsort)->get_sort(), intsort);
  // not an integer, which MathSAT and Yices2 would give sort Int
  EXPECT_EQ(s->make_term("1/2", realsort)->get_sort(), realsort);
  Term u = s->make_symbol("u", realsort);
  EXPECT_EQ(s->make_term(Is_Int, u)->get_sort(), boolsort);
}

TEST_P(UnitTermArithTests, NegatedValueIsDifferent)
{
  EXPECT_NE(s->make_term(2, intsort), s->make_term(-2, intsort));
  EXPECT_NE(s->make_term(2, realsort), s->make_term(-2, realsort));
}

TEST_P(UnitTermArithTests, MalformedIntStringThrows)
{
  for (const char * val : { "abc", "", "-", "1/2", "1.5" })
  {
    SCOPED_TRACE(val);
    EXPECT_THROW(s->make_term(val, intsort), IncorrectUsageException);
  }
}

TEST_P(UnitTermArithTests, MalformedRealStringThrows)
{
  for (const char * val : { "abc", "", "-", "1/", "1.2.3" })
  {
    SCOPED_TRACE(val);
    EXPECT_THROW(s->make_term(val, realsort), IncorrectUsageException);
  }
}

TEST_P(UnitTermArithTests, RealStringValues)
{
  s->set_opt("incremental", "true");
  // each string, and the numerator and denominator of its value
  const std::vector<std::tuple<const char *, int64_t, int64_t>> cases = {
    { "5", 5, 1 },     { "-5", -5, 1 }, { "1.5", 3, 2 },
    { "-1.5", -3, 2 }, { "1/2", 1, 2 }, { "-1/2", -1, 2 },
  };
  for (const auto & [val, num, den] : cases)
  {
    SCOPED_TRACE(val);
    Term expected = s->make_term(
        Div, s->make_term(num, realsort), s->make_term(den, realsort));
    s->push();
    s->assert_formula(s->make_term(
        Not, s->make_term(Equal, s->make_term(val, realsort), expected)));
    EXPECT_TRUE(s->check_sat().is_unsat());
    s->pop();
  }
}

TEST_P(UnitTermArithTests, SpacedFractionString)
{
  // as TermTranslator writes a fraction
  Term half =
      s->make_term(Div, s->make_term(1, realsort), s->make_term(2, realsort));
  s->assert_formula(s->make_term(
      Not, s->make_term(Equal, s->make_term("1 / 2", realsort), half)));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST_P(UnitTermArithTests, ToReal)
{
  Term i = s->make_symbol("i", intsort);
  Term x = s->make_symbol("x", realsort);
  s->assert_formula(s->make_term(Equal, x, s->make_term(To_Real, i)));
  s->assert_formula(s->make_term(Equal, i, s->make_term(2, intsort)));
  s->assert_formula(s->make_term(Distinct, x, s->make_term(2, realsort)));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST_P(UnitTermArithTests, IteOverIntegerValuedReal)
{
  // MathSAT and Yices2 make 0.0 an Int and 1/10 a Real
  s->set_opt("incremental", "true");
  Term b = s->make_symbol("b", boolsort);
  Term x = s->make_symbol("x", realsort);
  Term zero = s->make_term("0.0", realsort);
  Term tenth = s->make_term("1/10", realsort);
  Term not_b = s->make_term(Not, b);
  for (const Term & ite : { s->make_term(Ite, b, zero, tenth),
                            s->make_term(Ite, not_b, tenth, zero) })
  {
    SCOPED_TRACE(ite->to_string());
    EXPECT_EQ(ite->get_sort(), realsort);
    s->push();
    s->assert_formula(s->make_term(Equal, x, ite));
    s->assert_formula(b);
    s->assert_formula(s->make_term(Gt, x, zero));
    EXPECT_TRUE(s->check_sat().is_unsat());
    s->pop();
    s->push();
    s->assert_formula(s->make_term(Equal, x, ite));
    s->assert_formula(not_b);
    s->assert_formula(s->make_term(Lt, x, tenth));
    EXPECT_TRUE(s->check_sat().is_unsat());
    s->pop();
  }
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnitTerm,
                         UnitTermTests,
                         testing::ValuesIn(available_solver_configurations()));

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnitTermArith,
                         UnitTermArithTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { THEORY_INT, THEORY_REAL })));

class NegativeValueTests
    : public ::testing::Test,
      public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override { s = create_solver(GetParam()); }
  SmtSolver s;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(NegativeBVTests);
class NegativeBVTests : public NegativeValueTests
{
 protected:
  void SetUp() override
  {
    NegativeValueTests::SetUp();
    bvsort = s->make_sort(BV, 8);
  }
  Sort bvsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(NegativeIntTests);
class NegativeIntTests : public NegativeValueTests
{
 protected:
  void SetUp() override
  {
    NegativeValueTests::SetUp();
    intsort = s->make_sort(INT);
  }
  Sort intsort;
};

TEST_P(NegativeBVTests, IntAndStringAgree)
{
  EXPECT_EQ(s->make_term(-4, bvsort), s->make_term("-4", bvsort));
}

TEST_P(NegativeBVTests, OutOfRangeThrows)
{
  EXPECT_THROW(s->make_term("-129", bvsort), IncorrectUsageException);
}

// An 8-bit string may be read unsigned or signed, so -128..255 fit.
TEST_P(NegativeBVTests, UnsignedStringsAtTheEndsOfTheRange)
{
  for (int base : { 2, 10, 16 })
  {
    SCOPED_TRACE("base " + std::to_string(base));
    const char * max = base == 2 ? "11111111" : base == 10 ? "255" : "ff";
    const char * above = base == 2 ? "100000000" : base == 10 ? "256" : "100";
    EXPECT_EQ(s->make_term(max, bvsort, base), s->make_term(255, bvsort));
    EXPECT_THROW(s->make_term(above, bvsort, base), IncorrectUsageException);
  }
}

TEST_P(NegativeBVTests, SignedStringsAtTheEndsOfTheRange)
{
  if (GetParam().solver_enum == BZLA)
  {
    GTEST_SKIP() << "Bitwuzla rejects negative base 2 and 16 strings";
  }
  for (int base : { 2, 10, 16 })
  {
    SCOPED_TRACE("base " + std::to_string(base));
    const char * min = base == 2 ? "-10000000" : base == 10 ? "-128" : "-80";
    const char * below = base == 2 ? "-10000001" : base == 10 ? "-129" : "-81";
    EXPECT_EQ(s->make_term(min, bvsort, base), s->make_term(-128, bvsort));
    EXPECT_THROW(s->make_term(below, bvsort, base), IncorrectUsageException);
  }
}

TEST_P(NegativeBVTests, CancelsItsPositive)
{
  Term sum =
      s->make_term(BVAdd, s->make_term(4, bvsort), s->make_term(-4, bvsort));
  s->assert_formula(
      s->make_term(Not, s->make_term(Equal, sum, s->make_term(0, bvsort))));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST_P(NegativeIntTests, IntAndStringAgree)
{
  EXPECT_EQ(s->make_term(-5, intsort), s->make_term("-5", intsort));
}

TEST_P(NegativeIntTests, CancelsItsPositive)
{
  Term sum =
      s->make_term(Plus, s->make_term(5, intsort), s->make_term(-5, intsort));
  s->assert_formula(
      s->make_term(Not, s->make_term(Equal, sum, s->make_term(0, intsort))));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

INSTANTIATE_TEST_SUITE_P(
    ,
    NegativeBVTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_BV })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ,
    NegativeIntTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_INT })),
    ConfigName());

}  // namespace
