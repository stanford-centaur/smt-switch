/*********************                                                        */
/*! \file test-str.cpp
** \verbatim
** Top contributors (to current version):
**  Nestan Tsiskaridze
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
** Tests for theory of strings.
**/

#include <utility>
#include <vector>

#include "available_solvers.h"
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(StrTests);
class StrTests : public ::testing::Test,
                 public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    s->set_opt("incremental", "true");
  }
  SmtSolver s;
};

TEST_P(StrTests, StrChildren)
{
  Sort strsort = s->make_sort(STRING);

  Term t = s->make_symbol("t", strsort);
  Term w = s->make_symbol("w", strsort);
  Term strA = s->make_term("A", false, strsort);

  EXPECT_TRUE(t->get_op().is_null());
  EXPECT_TRUE(t->is_symbolic_const());
  EXPECT_FALSE(t->is_value());
  EXPECT_TRUE(w->is_symbolic_const());
  EXPECT_FALSE(w->is_value());
  EXPECT_FALSE(strA->is_symbolic_const());
  EXPECT_TRUE(strA->is_value());

  Term tA = s->make_term(StrConcat, t, strA);
  EXPECT_EQ(tA->get_op(), StrConcat);
  TermVec children_tA;
  for (auto tt : tA)
  {
    children_tA.push_back(tt);
  }
  EXPECT_EQ(children_tA[0], t);
  EXPECT_EQ(children_tA[1], strA);

  Term tw = s->make_term(StrConcat, t, w);
  EXPECT_EQ(tw->get_op(), StrConcat);
  TermVec children_tw;
  for (auto tt : tw)
  {
    children_tw.push_back(tt);
  }
  EXPECT_EQ(children_tw[0], t);
  EXPECT_EQ(children_tw[1], w);
}

TEST_P(StrTests, EqualVars)
{
  Sort str_sort = s->make_sort(STRING);
  Term x1 = s->make_symbol("x1", str_sort);
  Term x2 = s->make_symbol("x2", str_sort);
  s->assert_formula(s->make_term(Equal, x1, x2));
  s->check_sat();
  std::string strx1 = s->get_value(x1)->to_string();
  std::string strx2 = s->get_value(x2)->to_string();
  ASSERT_EQ(strx1, strx2);
}

TEST_P(StrTests, EqualStrConsts)
{
  Sort str_sort = s->make_sort(STRING);
  Term x1 = s->make_term("A", false, str_sort);
  Term x2 = s->make_term("A", false, str_sort);
  s->check_sat();
  std::string strx1 = s->get_value(x1)->to_string();
  std::string strx2 = s->get_value(x2)->to_string();
  ASSERT_EQ(strx1, strx2);
}

TEST_P(StrTests, UseEscSequences)
{
  Sort str_sort = s->make_sort(STRING);

  Term x1 = s->make_term("\\u{0021}", true, str_sort);
  Term x2 = s->make_term("\\u2200", true, str_sort);
  Term x3 = s->make_term("\\u2102", false, str_sort);
  Term x4 = s->make_term("\\u{10}", false, str_sort);

  s->check_sat();

  std::wstring wchar_u = L"u";
  std::wstring wstrx1 = s->get_value(x1)->getStringValue();
  std::wstring wstrx2 = s->get_value(x2)->getStringValue();
  std::wstring wstrx3 = s->get_value(x3)->getStringValue();
  std::wstring wstrx4 = s->get_value(x4)->getStringValue();

  EXPECT_EQ(wstrx1.find(wchar_u), std::wstring::npos);
  EXPECT_EQ(wstrx2.find(wchar_u), std::wstring::npos);
  EXPECT_NE(wstrx3.find(wchar_u), std::wstring::npos);
  EXPECT_NE(wstrx4.find(wchar_u), std::wstring::npos);
}

TEST_P(StrTests, EqualVarStrVals)
{
  Sort str_sort = s->make_sort(STRING);
  Term x1 = s->make_symbol("x1", str_sort);
  Term x2 = s->make_symbol("x2", str_sort);
  Term A = s->make_term("A", false, str_sort);
  s->assert_formula(s->make_term(Equal, x1, A));
  s->assert_formula(s->make_term(Equal, x2, A));
  s->check_sat();
  std::string strx1 = s->get_value(x1)->to_string();
  std::string strx2 = s->get_value(x2)->to_string();
  ASSERT_EQ(strx1, strx2);
}

TEST_P(StrTests, EqualWStrConsts)
{
  Sort str_sort = s->make_sort(STRING);
  Term x1 = s->make_term(L"A", str_sort);
  Term x2 = s->make_term(L"A", str_sort);
  s->check_sat();
  std::string strx1 = s->get_value(x1)->to_string();
  std::string strx2 = s->get_value(x2)->to_string();
  ASSERT_EQ(strx1, strx2);
}

TEST_P(StrTests, EqualVarWStrVals)
{
  Sort str_sort = s->make_sort(STRING);
  Term x1 = s->make_symbol("x1", str_sort);
  Term x2 = s->make_symbol("x2", str_sort);
  Term A = s->make_term(L"A", str_sort);
  s->assert_formula(s->make_term(Equal, x1, A));
  s->assert_formula(s->make_term(Equal, x2, A));
  s->check_sat();
  std::string strx1 = s->get_value(x1)->to_string();
  std::string strx2 = s->get_value(x2)->to_string();
  ASSERT_EQ(strx1, strx2);
}

TEST_P(StrTests, StringOperators)
{
  s->set_logic("QF_SLIA");
  Sort strsort = s->make_sort(STRING);
  Sort intsort = s->make_sort(INT);

  Term zero = s->make_term(0, intsort);
  Term one = s->make_term(1, intsort);
  Term minusone = s->make_term(-1, intsort);
  Term A = s->make_term("A", false, strsort);
  Term str1 = s->make_term("1", false, strsort);
  Term str10 = s->make_term("10", false, strsort);

  Term x = s->make_symbol("x", strsort);
  Term y = s->make_symbol("y", strsort);
  Term z = s->make_symbol("z", strsort);
  Term empty = s->make_symbol("empty", strsort);

  Term lenx = s->make_term(StrLen, x);
  Term leny = s->make_term(StrLen, y);
  Term lenz = s->make_term(StrLen, z);
  Term lenempty = s->make_term(StrLen, empty);

  Term xx = s->make_term(StrConcat, x, x);
  Term xy = s->make_term(StrConcat, x, y);
  Term yx = s->make_term(StrConcat, y, x);
  Term xxx = s->make_term(StrConcat, xx, x);
  Term xyy = s->make_term(StrConcat, xy, y);

  Term substryx = s->make_term(StrSubstr, yx, leny, lenx);

  TermVec constraints;
  constraints.push_back(s->make_term(Equal, lenempty, zero));

  // StrLt
  constraints.push_back(s->make_term(StrLt, x, y));
  constraints.push_back(s->make_term(StrLt, yx, xy));
  // StrLeq StrConcat
  constraints.push_back(s->make_term(StrLeq, z, xy));
  // StrLen
  constraints.push_back(s->make_term(Lt, zero, lenz));
  // StrConcat
  constraints.push_back(s->make_term(Not, s->make_term(Equal, xy, yx)));
  // StrSubstr
  constraints.push_back(s->make_term(Equal, x, substryx));
  constraints.push_back(s->make_term(Not, s->make_term(Equal, y, substryx)));
  constraints.push_back(
      s->make_term(Equal, empty, s->make_term(StrSubstr, x, lenx, lenx)));
  constraints.push_back(
      s->make_term(Equal, empty, s->make_term(StrSubstr, x, minusone, lenx)));
  // StrAt
  constraints.push_back(s->make_term(
      Equal, s->make_term(StrLen, s->make_term(StrAt, y, zero)), one));
  constraints.push_back(
      s->make_term(Equal, empty, s->make_term(StrAt, x, lenx)));
  constraints.push_back(
      s->make_term(Equal, empty, s->make_term(StrAt, x, minusone)));
  // StrContains
  constraints.push_back(s->make_term(Not, s->make_term(StrContains, x, y)));
  constraints.push_back(s->make_term(StrContains, xy, y));
  // StrIndexof
  constraints.push_back(s->make_term(
      Equal,
      lenx,
      s->make_term(StrIndexof, xyy, y, s->make_term(Minus, lenx, one))));
  constraints.push_back(
      s->make_term(Equal, zero, s->make_term(StrIndexof, xy, empty, zero)));
  constraints.push_back(
      s->make_term(Equal, minusone, s->make_term(StrIndexof, xy, x, minusone)));
  constraints.push_back(
      s->make_term(Equal, minusone, s->make_term(StrIndexof, x, y, lenx)));
  constraints.push_back(
      s->make_term(Equal, minusone, s->make_term(StrIndexof, x, y, zero)));
  // StrReplace
  constraints.push_back(
      s->make_term(Equal, xx, s->make_term(StrReplace, xy, y, x)));
  constraints.push_back(
      s->make_term(Equal, xy, s->make_term(StrReplace, y, empty, x)));
  // StrReplaceAll
  constraints.push_back(
      s->make_term(Equal, xxx, s->make_term(StrReplaceAll, xyy, y, x)));
  constraints.push_back(
      s->make_term(Equal, xyy, s->make_term(StrReplaceAll, xyy, empty, x)));
  // StrPrefixof
  constraints.push_back(s->make_term(StrPrefixof, x, xyy));
  constraints.push_back(s->make_term(Not, s->make_term(StrPrefixof, str1, A)));
  // StrSuffixof
  constraints.push_back(s->make_term(StrSuffixof, y, xyy));
  constraints.push_back(s->make_term(Not, s->make_term(StrSuffixof, str1, A)));
  // StrIsDigit
  constraints.push_back(s->make_term(StrIsDigit, str1));
  constraints.push_back(s->make_term(Not, s->make_term(StrIsDigit, A)));
  constraints.push_back(s->make_term(Not, s->make_term(StrIsDigit, str10)));

  for (const Term & c : constraints)
  {
    s->assert_formula(c);
  }

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  // the length constraint forces empty to be the empty string
  EXPECT_EQ(s->get_value(empty), s->make_term("", false, strsort));
  // the rest of the model is not unique, so check it satisfies each constraint
  Term true_term = s->make_term(true);
  for (const Term & c : constraints)
  {
    EXPECT_EQ(s->get_value(c), true_term);
  }
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverStrTests,
                         StrTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { THEORY_INT, THEORY_STR })));

}  // namespace
