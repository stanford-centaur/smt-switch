/*********************                                                        */
/*! \file cvc5-incremental.cpp
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
  s->set_logic("QF_BV");
  s->set_opt("produce-models", "true");
  s->set_opt("incremental", "true");

  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term y = s->make_symbol("y", bvsort8);
  Term z = s->make_symbol("z", bvsort8);

  Term a = s->make_term(Equal, z, s->make_term(BVAdd, y, z));
  Term b = s->make_term(Equal, z, s->make_term(BVSub, y, z));
  s->assert_formula(a);
  s->assert_formula(b);

  Result r = s->check_sat();
  assert(r.is_sat());

  Term assumption0 =
      s->make_term(And,
                   s->make_term(Distinct, x, s->make_term(0, bvsort8)),
                   s->make_term(Distinct, y, s->make_term(0, bvsort8)));

  Sort boolsort = s->make_sort(BOOL);
  Term il0 = s->make_symbol("il0", boolsort);
  s->assert_formula(s->make_term(Implies, il0, assumption0));
  r = s->check_sat_assuming(TermVec{ il0 });

  Term assumption1 = s->make_term(Equal, x, s->make_term(1, bvsort8));
  Term il1 = s->make_symbol("il1", boolsort);
  s->assert_formula(s->make_term(Implies, il1, assumption1));
  r = s->check_sat_assuming({ il1 });
  assert(r.is_sat());
  assert(s->get_value(x)->to_int() == 1);

  s->push();
  s->assert_formula(assumption0);
  r = s->check_sat();
  assert(r.is_unsat());
  s->pop();

  r = s->check_sat();
  assert(r.is_sat());

  s->reset_assertions();
  s->assert_formula(assumption0);
  r = s->check_sat();
  assert(r.is_sat());

  return 0;
}
