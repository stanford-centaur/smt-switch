/*********************                                                        */
/*! \file cvc5-indexed-op-tests.cpp
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
#include <memory>
#include <vector>

#include "assert.h"
#include "cvc5_factory.h"
#include "smt.h"
// after full installation
// #include "smt-switch/cvc5_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = Cvc5SolverFactory::create(false);
  s->set_opt("produce-models", "true");
  Sort bvsort9 = s->make_sort(BV, 9);
  Term x = s->make_symbol("x", bvsort9);
  Term y = s->make_symbol("y", bvsort9);
  Term onebit = s->make_symbol("onebit", s->make_sort(BV, 1));

  Term unnecessary_rotation = s->make_term(Op(Rotate_Right, 1), onebit);

  Op ext74 = Op(Extract, 7, 4);
  Term x_upper = s->make_term(ext74, x);

  Term y_ror = s->make_term(Op(Rotate_Right, 2), y);
  Term y_rol = s->make_term(Op(Rotate_Left, 2), y);

  s->assert_formula(s->make_term(Equal, y_ror, y_rol));
  s->assert_formula(s->make_term(Distinct, y, s->make_term(0, bvsort9)));
  s->assert_formula(s->make_term(
      Equal, x, s->make_term(Op(Repeat, 9), unnecessary_rotation)));

  Result r = s->check_sat();
  assert(r.is_sat());

  Term xc = s->get_value(x);
  Term x_upperc = s->get_value(x_upper);
  Term yc = s->get_value(y);

  cout << "Results:" << endl;
  cout << "\tx = " << xc->to_int() << endl;
  cout << "\tx[7:4] = " << x_upperc->to_int() << endl;
  cout << "\ty = " << yc->to_int() << endl;
  return 0;
}
