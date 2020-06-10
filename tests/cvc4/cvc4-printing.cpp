/*********************                                                        */
/*! \file cvc4-printinh.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
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
#include <sstream>
#include "assert.h"

#include "cvc4_factory.h"
#include "printing_solver.h"
#include "smt.h"
// after full installation
// #include "smt-switch/cvc4_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  stringbuf strbuf;
  SmtSolver cvc4 = CVC4SolverFactory::create(false);
  ostream os(&strbuf);
  SmtSolver s = create_printing_solver(cvc4, &os, PrintingStyleEnum::DEFAULT);
  s->set_logic("QF_AUFBV");
  s->set_opt("produce-models", "true");
  s->set_opt("incremental", "true");
  s->set_opt("produce-unsat-assumptions", "true");
  Sort us = s->make_sort("S", 0);
  Sort bvsort32 = s->make_sort(BV, 32);
  Sort fun_sort = s->make_sort(FUNCTION, SortVec{bvsort32,us});
  Sort array32_32 = s->make_sort(ARRAY, bvsort32, bvsort32);
  Term x = s->make_symbol("x", bvsort32);
  Term y = s->make_symbol("y", bvsort32);
  Term arr = s->make_symbol("arr", array32_32);
  Term fun = s->make_symbol("f", fun_sort);
  
  Term S0 = s->make_symbol("s", us);

  Term ind1 = s->make_symbol("ind1", s->make_sort(BOOL));
  Term f = s->make_term(Equal, s->make_term(Apply, fun, x), S0 );
  s->assert_formula(ind1);
  s->assert_formula(s->make_term(Equal, ind1, f));
  s->assert_formula(f);
  s->assert_formula(
      s->make_term(Not,
                   s->make_term(Implies,
                                s->make_term(Equal, x, y),
                                s->make_term(Equal,
                                             s->make_term(Select, arr, x),
                                             s->make_term(Select, arr, y)))));
  assert(!s->check_sat_assuming(TermVec{ind1}).is_sat());
  TermVec usc = s->get_unsat_core();
  cout << strbuf.str() << endl;
  return 0;
}
