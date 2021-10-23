/*********************                                                        */
/*! \file yices2-incremental.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
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
#include "smt.h"
#include "yices2_factory.h"
// after full installation
// #include "smt-switch/cvc5_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = Yices2SolverFactory::create(true);
  s->set_logic("QF_BV");
  s->set_opt("produce-models", "true");
  s->set_opt("incremental", "true");

  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term y = s->make_symbol("y", bvsort8);
  Term z = s->make_symbol("z", bvsort8);

  s->assert_formula(s->make_term(Equal, z, s->make_term(BVAdd, y, z)));
  s->assert_formula(s->make_term(Equal, z, s->make_term(BVSub, y, z)));
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
  assert(r.is_unsat());

  Term il1 = s->make_symbol("il1", boolsort);
  Term assumption1 = s->make_term(Equal, x, s->make_term(1, bvsort8));
  s->assert_formula(s->make_term(Implies, il1, assumption1));
  r = s->check_sat_assuming({ il1 });
  assert(r.is_sat());
  assert(s->get_value(x)->to_int() == 1);

  s->push();
  s->assert_formula(assumption0);
  r = s->check_sat();
  // TODO: Not sure if Yices problem or implementation problem.
  // assert(r.is_unsat());
  s->pop();

  r = s->check_sat();
  assert(r.is_sat());

  s->reset_assertions();
  s->assert_formula(assumption0);
  r = s->check_sat();
  assert(r.is_sat());

  return 0;
}
