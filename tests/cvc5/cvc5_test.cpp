/*********************                                                        */
/*! \file cvc5_test.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
**
**
**/

#include <iostream>

#include "cvc5_factory.h"
#include "smt.h"
// after full installation
// #include "smt-switch/cvc5_factory.h"
// #include "smt-switch/smt.h"

using namespace std;
using namespace smt;

int main()
{
  SmtSolver s = Cvc5SolverFactory::create(false);
  Term x = s->make_symbol("x", s->make_sort(BV, 8));
  Term y = s->make_symbol("y", s->make_sort(BV, 8));
  cout << x->to_string() << endl;
  cout << y->to_string() << endl;
  Term xpy = s->make_term(BVAdd, x, y);
  cout << xpy->to_string() << endl;
  Term xext = s->make_term(Op(Extract, 3, 0), x);
  cout << xext << endl;
  Term _true = s->make_term(true);
  cout << _true << endl;
  Term _one = s->make_term(1, s->make_sort(INT));
  cout << _one << endl;
  Term _one_r = s->make_term("1.0", s->make_sort(REAL));
  cout << _one_r << endl;
  Term _two_bv = s->make_term(2, s->make_sort(BV, 4));
  cout << _two_bv << endl;
  Term _three_bv = s->make_term("3", s->make_sort(BV, 4));
  cout << _three_bv << endl;

  cout << "Children of " << xpy << endl;
  for (auto c : xpy)
  {
    cout << "\t" << c << endl;
  }

  Term str_a = s->make_term("a", false, s->make_sort(STRING));
  cout << str_a << endl;
  Term wstr_b = s->make_term(L"b", s->make_sort(STRING));
  cout << wstr_b << endl;
  Term t = s->make_symbol("t", s->make_sort(STRING));
  Term w = s->make_symbol("w", s->make_sort(STRING));
  cout << t->to_string() << endl;
  cout << w->to_string() << endl;
  Term tw = s->make_term(StrConcat, t, w);
  cout << tw->to_string() << endl;
  cout << tw << endl;
  cout << "Children of " << tw << endl;
  for (auto c : tw)
  {
    cout << "\t" << c << endl;
  }  

  return 0;
}
