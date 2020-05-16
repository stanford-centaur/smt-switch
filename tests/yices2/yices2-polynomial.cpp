/*********************                                                        */
/*! \file yices2-polynomial.cpp
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

#include "gmp.h"
#include "yices.h"
#include "yices2_sort.h"
#include "yices2_term.h"

#include "smt.h"
#include "yices2_factory.h"
// after a full installation
// #include "smt-switch/msat_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = Yices2SolverFactory::create(true);
  s->set_opt("produce-models", "true");
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term y = s->make_symbol("y", bvsort8);
  Term z = s->make_symbol("z", bvsort8);

  Term a = s->make_symbol("a", s->make_sort(INT));
  Term b = s->make_symbol("b", s->make_sort(INT));
  Term c = s->make_symbol("c", s->make_sort(INT));

  Term constraint;

  constraint = s->make_term(
      Equal, c, s->make_term(Pow, b, s->make_term("4", s->make_sort(INT))));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, b));

  constraint = s->make_term(Equal, z, s->make_term(BVMul, x, y));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, b));

  constraint = s->make_term(Equal, z, s->make_term(BVAdd, x, y));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, b));

  constraint =
      s->make_term(Equal, z, s->make_term(BVAdd, x, s->make_term(BVMul, y, z)));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, b));

  constraint =
      s->make_term(Equal, z, s->make_term(BVAdd, x, s->make_term(BVMul, y, z)));
  constraint = s->make_term(
      And,
      constraint,
      s->make_term(Equal,
                   a,
                   s->make_term(Pow, b, s->make_term("4", s->make_sort(INT)))));

  Term bv_sum = s->make_term(BVAdd, x, s->make_term(BVMul, y, z));
  // cout << "bv sum : " << bv_sum << endl;
  constraint = s->make_term(Equal, z, bv_sum);

  c = s->make_term("3", s->make_sort(INT));

  constraint = s->make_term(
      And, constraint, s->make_term(Equal, a, s->make_term(Pow, b, c)));

  Term d = s->make_symbol("d", s->make_sort(INT));

  constraint = s->make_term(
      Equal, s->make_term("100", s->make_sort(INT)), s->make_term(Plus, b, d));

  constraint =
      s->make_term(And,
                   constraint,
                   s->make_term(Ge, b, s->make_term("12", s->make_sort(INT))));

  constraint = s->make_term(
      Equal,
      s->make_term("100", s->make_sort(INT)),
      s->make_term(Plus, b, s->make_term("55", s->make_sort(INT))));

  constraint =
      s->make_term(And,
                   constraint,
                   s->make_term(Ge, b, s->make_term("12", s->make_sort(INT))));

  return 0;
}
