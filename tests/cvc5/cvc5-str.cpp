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

  Term x = s->make_symbol("x", strsort);
  Term y = s->make_symbol("y", strsort);
  Term z = s->make_symbol("z", strsort);

  Term lenx = s->make_term(StrLen, x);
  Term leny = s->make_term(StrLen, y);
  Term lenz = s->make_term(StrLen, z);

  Term xy = s->make_term(StrConcat, x, y);
  Term yx = s->make_term(StrConcat, y, x);

  //StrLt
  s->assert_formula(s->make_term(StrLt, x, y));
  s->assert_formula(s->make_term(StrLt, yx, xy));
  //StrLeq StrConcat
  s->assert_formula(s->make_term(StrLeq, z, xy));
  //StrLen
  s->assert_formula(s->make_term(Lt, zero, lenz));
  //StrConcat
  s->assert_formula(s->make_term(Not, s->make_term(Equal, xy, yx)));



  Result r = s->check_sat();
  assert(r.is_sat());

  cout << "Model Values:" << endl;
  for (auto t : TermVec({ x, y, z }))
  {
    cout << "\t" << t << " = " << s->get_value(t) << endl;
  }
  return 0;
}
