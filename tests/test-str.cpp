/*!
 * \file test-str.cpp
 * \brief Tests for theory of strings
 * \author Nestan Tsiskaridze
 * \date 2023
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
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt::tests {

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(StrTests);
class StrTests : public testing::Test,
                 public testing::WithParamInterface<SolverConfiguration>
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
  Sort strsort = s->make_sort(SortKind::STRING);

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

  Term tA = s->make_term(Op::StrConcat, t, strA);
  EXPECT_EQ(tA->get_op(), Op::StrConcat);
  TermVec children_tA;
  for (auto tt : tA)
  {
    children_tA.push_back(tt);
  }
  EXPECT_EQ(children_tA[0], t);
  EXPECT_EQ(children_tA[1], strA);

  Term tw = s->make_term(Op::StrConcat, t, w);
  EXPECT_EQ(tw->get_op(), Op::StrConcat);
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
  Sort str_sort = s->make_sort(SortKind::STRING);
  Term x1 = s->make_symbol("x1", str_sort);
  Term x2 = s->make_symbol("x2", str_sort);
  s->assert_formula(s->make_term(Op::Equal, x1, x2));
  s->check_sat();
  std::string strx1 = s->get_value(x1)->to_string();
  std::string strx2 = s->get_value(x2)->to_string();
  ASSERT_EQ(strx1, strx2);
}

TEST_P(StrTests, EqualStrConsts)
{
  Sort str_sort = s->make_sort(SortKind::STRING);
  Term x1 = s->make_term("A", false, str_sort);
  Term x2 = s->make_term("A", false, str_sort);
  s->check_sat();
  std::string strx1 = s->get_value(x1)->to_string();
  std::string strx2 = s->get_value(x2)->to_string();
  ASSERT_EQ(strx1, strx2);
}

TEST_P(StrTests, UseEscSequences)
{
  Sort str_sort = s->make_sort(SortKind::STRING);

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
  Sort str_sort = s->make_sort(SortKind::STRING);
  Term x1 = s->make_symbol("x1", str_sort);
  Term x2 = s->make_symbol("x2", str_sort);
  Term A = s->make_term("A", false, str_sort);
  s->assert_formula(s->make_term(Op::Equal, x1, A));
  s->assert_formula(s->make_term(Op::Equal, x2, A));
  s->check_sat();
  std::string strx1 = s->get_value(x1)->to_string();
  std::string strx2 = s->get_value(x2)->to_string();
  ASSERT_EQ(strx1, strx2);
}

TEST_P(StrTests, EqualWStrConsts)
{
  Sort str_sort = s->make_sort(SortKind::STRING);
  Term x1 = s->make_term(L"A", str_sort);
  Term x2 = s->make_term(L"A", str_sort);
  s->check_sat();
  std::string strx1 = s->get_value(x1)->to_string();
  std::string strx2 = s->get_value(x2)->to_string();
  ASSERT_EQ(strx1, strx2);
}

TEST_P(StrTests, EqualVarWStrVals)
{
  Sort str_sort = s->make_sort(SortKind::STRING);
  Term x1 = s->make_symbol("x1", str_sort);
  Term x2 = s->make_symbol("x2", str_sort);
  Term A = s->make_term(L"A", str_sort);
  s->assert_formula(s->make_term(Op::Equal, x1, A));
  s->assert_formula(s->make_term(Op::Equal, x2, A));
  s->check_sat();
  std::string strx1 = s->get_value(x1)->to_string();
  std::string strx2 = s->get_value(x2)->to_string();
  ASSERT_EQ(strx1, strx2);
}

TEST_P(StrTests, StringOperators)
{
  s->set_logic("QF_SLIA");
  Sort strsort = s->make_sort(SortKind::STRING);
  Sort intsort = s->make_sort(SortKind::INT);

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

  Term lenx = s->make_term(Op::StrLen, x);
  Term leny = s->make_term(Op::StrLen, y);
  Term lenz = s->make_term(Op::StrLen, z);
  Term lenempty = s->make_term(Op::StrLen, empty);

  Term xx = s->make_term(Op::StrConcat, x, x);
  Term xy = s->make_term(Op::StrConcat, x, y);
  Term yx = s->make_term(Op::StrConcat, y, x);
  Term xxx = s->make_term(Op::StrConcat, xx, x);
  Term xyy = s->make_term(Op::StrConcat, xy, y);

  Term substryx = s->make_term(Op::StrSubstr, yx, leny, lenx);

  TermVec constraints;
  constraints.push_back(s->make_term(Op::Equal, lenempty, zero));

  // StrLt
  constraints.push_back(s->make_term(Op::StrLt, x, y));
  constraints.push_back(s->make_term(Op::StrLt, yx, xy));
  // StrLeq StrConcat
  constraints.push_back(s->make_term(Op::StrLeq, z, xy));
  // StrLen
  constraints.push_back(s->make_term(Op::Lt, zero, lenz));
  // StrConcat
  constraints.push_back(s->make_term(Op::Not, s->make_term(Op::Equal, xy, yx)));
  // StrSubstr
  constraints.push_back(s->make_term(Op::Equal, x, substryx));
  constraints.push_back(
      s->make_term(Op::Not, s->make_term(Op::Equal, y, substryx)));
  constraints.push_back(s->make_term(
      Op::Equal, empty, s->make_term(Op::StrSubstr, x, lenx, lenx)));
  constraints.push_back(s->make_term(
      Op::Equal, empty, s->make_term(Op::StrSubstr, x, minusone, lenx)));
  // StrAt
  constraints.push_back(
      s->make_term(Op::Equal,
                   s->make_term(Op::StrLen, s->make_term(Op::StrAt, y, zero)),
                   one));
  constraints.push_back(
      s->make_term(Op::Equal, empty, s->make_term(Op::StrAt, x, lenx)));
  constraints.push_back(
      s->make_term(Op::Equal, empty, s->make_term(Op::StrAt, x, minusone)));
  // StrContains
  constraints.push_back(
      s->make_term(Op::Not, s->make_term(Op::StrContains, x, y)));
  constraints.push_back(s->make_term(Op::StrContains, xy, y));
  // StrIndexof
  constraints.push_back(s->make_term(
      Op::Equal,
      lenx,
      s->make_term(
          Op::StrIndexof, xyy, y, s->make_term(Op::Minus, lenx, one))));
  constraints.push_back(s->make_term(
      Op::Equal, zero, s->make_term(Op::StrIndexof, xy, empty, zero)));
  constraints.push_back(s->make_term(
      Op::Equal, minusone, s->make_term(Op::StrIndexof, xy, x, minusone)));
  constraints.push_back(s->make_term(
      Op::Equal, minusone, s->make_term(Op::StrIndexof, x, y, lenx)));
  constraints.push_back(s->make_term(
      Op::Equal, minusone, s->make_term(Op::StrIndexof, x, y, zero)));
  // StrReplace
  constraints.push_back(
      s->make_term(Op::Equal, xx, s->make_term(Op::StrReplace, xy, y, x)));
  constraints.push_back(
      s->make_term(Op::Equal, xy, s->make_term(Op::StrReplace, y, empty, x)));
  // StrReplaceAll
  constraints.push_back(
      s->make_term(Op::Equal, xxx, s->make_term(Op::StrReplaceAll, xyy, y, x)));
  constraints.push_back(s->make_term(
      Op::Equal, xyy, s->make_term(Op::StrReplaceAll, xyy, empty, x)));
  // StrPrefixof
  constraints.push_back(s->make_term(Op::StrPrefixof, x, xyy));
  constraints.push_back(
      s->make_term(Op::Not, s->make_term(Op::StrPrefixof, str1, A)));
  // StrSuffixof
  constraints.push_back(s->make_term(Op::StrSuffixof, y, xyy));
  constraints.push_back(
      s->make_term(Op::Not, s->make_term(Op::StrSuffixof, str1, A)));
  // StrIsDigit
  constraints.push_back(s->make_term(Op::StrIsDigit, str1));
  constraints.push_back(s->make_term(Op::Not, s->make_term(Op::StrIsDigit, A)));
  constraints.push_back(
      s->make_term(Op::Not, s->make_term(Op::StrIsDigit, str10)));

  for (const Term & c : constraints)
  {
    s->assert_formula(c);
  }

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  // the length constraint forces empty to be the empty string
  EXPECT_EQ(s->get_value(empty), s->make_term("", false, strsort));
  // the rest of the model is not unique, so check it satisfies each constraint
  for (const Term & c : constraints)
  {
    EXPECT_TRUE(s->get_value(c)->to_bool());
  }
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverStrTests,
    StrTests,
    testing::ValuesIn(filter_solver_configurations_with_generic(
        { SolverAttribute::THEORY_INT, SolverAttribute::THEORY_STR })));

}  // namespace

}  // namespace smt::tests
