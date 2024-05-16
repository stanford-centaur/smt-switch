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

#include <iostream>
#include <memory>
#include <vector>

#include "assert.h"
#include "cvc5_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

int main()
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
  Term n = s->make_symbol("n", intsort);

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

  s->assert_formula(s->make_term(Equal, lenempty, zero));

  //StrLt
  s->assert_formula(s->make_term(StrLt, x, y));
  s->assert_formula(s->make_term(StrLt, yx, xy));
  //StrLeq StrConcat
  s->assert_formula(s->make_term(StrLeq, z, xy));
  //StrLen
  s->assert_formula(s->make_term(Lt, zero, lenz));
  //StrConcat
  s->assert_formula(s->make_term(Not, s->make_term(Equal, xy, yx)));
  //StrSubstr
  s->assert_formula(s->make_term(Equal, x, substryx));
  s->assert_formula(s->make_term(Not, s->make_term(Equal, y, substryx)));
  s->assert_formula(s->make_term(Equal, empty, s->make_term(StrSubstr, x, lenx, lenx)));
  s->assert_formula(s->make_term(Equal, empty, s->make_term(StrSubstr, x, minusone, lenx)));
  //StrAt
  s->assert_formula(s->make_term(Equal, s->make_term(StrLen, s->make_term(StrAt, y, zero)), one));
  s->assert_formula(s->make_term(Equal, empty, s->make_term(StrAt, x, lenx)));
  s->assert_formula(s->make_term(Equal, empty, s->make_term(StrAt, x, minusone)));
  //StrContains
  s->assert_formula(s->make_term(Not, s->make_term(StrContains, x, y)));
  s->assert_formula(s->make_term(StrContains, xy, y));
  //StrIndexof
  s->assert_formula(s->make_term(Equal, lenx, s->make_term(StrIndexof, xyy, y, s->make_term(Minus, lenx, one))));
  s->assert_formula(s->make_term(Equal, zero, s->make_term(StrIndexof, xy, empty, zero)));
  s->assert_formula(s->make_term(Equal, minusone, s->make_term(StrIndexof, xy, x, minusone)));
  s->assert_formula(s->make_term(Equal, minusone, s->make_term(StrIndexof, x, y, lenx)));
  s->assert_formula(s->make_term(Equal, minusone, s->make_term(StrIndexof, x, y, zero)));
  //StrReplace
  s->assert_formula(s->make_term(Equal, xx, s->make_term(StrReplace, xy, y, x)));
  s->assert_formula(s->make_term(Equal, xy, s->make_term(StrReplace, y, empty, x)));
  //StrReplaceAll
  s->assert_formula(s->make_term(Equal, xxx, s->make_term(StrReplaceAll, xyy, y, x)));
  s->assert_formula(s->make_term(Equal, xyy, s->make_term(StrReplaceAll, xyy, empty, x)));
  //StrPrefixof
  s->assert_formula(s->make_term(StrPrefixof, x, xyy));
  s->assert_formula(s->make_term(Not, s->make_term(StrPrefixof, str1, A)));
  //StrSuffixof
  s->assert_formula(s->make_term(StrSuffixof, y, xyy));
  s->assert_formula(s->make_term(Not, s->make_term(StrSuffixof, str1, A)));
  //StrIsDigit
  s->assert_formula(s->make_term(StrIsDigit, str1));
  s->assert_formula(s->make_term(Not, s->make_term(StrIsDigit, A)));
  s->assert_formula(s->make_term(Not, s->make_term(StrIsDigit, str10)));

  Result r = s->check_sat();
  assert(r.is_sat());

  cout << "Model Values:" << endl;
  for (auto t : TermVec({ x, y, z}))
  {
    cout << "\t" << t << " = " << s->get_value(t) << endl;
  }
  return 0;
}
