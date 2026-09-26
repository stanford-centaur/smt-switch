/*********************                                                        */
/*! \file cvc5-str.cpp
** \verbatim
** Top contributors (to current version):
**   Nestan Tsiskaridze
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
** Tests for strings in the cvc5 backend.
**/

#include <gtest/gtest.h>

#include <memory>
#include <vector>

#include "cvc5_factory.h"
#include "smt.h"

using namespace smt;

TEST(Cvc5Str, StringOperators)
{
  SmtSolver s = Cvc5SolverFactory::create(false);
  s->set_opt("produce-models", "true");
  s->set_logic("S");
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
