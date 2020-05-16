/*********************                                                        */
/*! \file msat-substitute.cpp
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

#include "msat_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/msat_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = MsatSolverFactory::create(false);
  s->set_logic("QF_ABV");
  s->set_opt("produce-models", "true");
  Sort bvsort4 = s->make_sort(BV, 4);
  Sort bvsort8 = s->make_sort(BV, 8);
  Sort array4_8 = s->make_sort(ARRAY, bvsort4, bvsort8);

  Term idx = s->make_symbol("idx", bvsort4);
  Term x = s->make_symbol("x", bvsort8);
  Term y = s->make_symbol("y", bvsort8);
  Term z = s->make_symbol("z", bvsort8);
  Term arr = s->make_symbol("arr", array4_8);

  UnorderedTermSet orig_set = { idx, x, y, z, arr };

  Term idx0 = s->make_symbol("idx0", bvsort4);
  Term x0 = s->make_symbol("x0", bvsort8);
  Term y0 = s->make_symbol("y0", bvsort8);
  Term z0 = s->make_symbol("z0", bvsort8);
  Term arr0 = s->make_symbol("arr0", array4_8);

  UnorderedTermSet timed_set = { idx0, x0, y0, z0, arr0 };

  Term constraint =
      s->make_term(Equal,
                   s->make_term(Select, arr, idx),
                   s->make_term(BVAdd, x, s->make_term(BVMul, y, z)));

  UnorderedTermSet visited;
  TermVec to_visit({ constraint });
  Term t;
  int num_consts = 0;
  while (to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();
    if (visited.find(t) == visited.end())
    {
      visited.insert(t);
      for (auto c : t)
      {
        to_visit.push_back(c);
      }

      if (t->is_symbolic_const())
      {
        num_consts++;
        cout << "checking " << t << endl;
        assert(orig_set.find(t) != orig_set.end());
      }
    }
  }
  assert(num_consts == orig_set.size());

  cout << endl;

  Term timed_constraint = s->substitute(
      constraint,
      UnorderedTermMap{
          { idx, idx0 }, { x, x0 }, { y, y0 }, { z, z0 }, { arr, arr0 } });

  visited.clear();
  to_visit.clear();
  to_visit.push_back(timed_constraint);
  num_consts = 0;
  while (to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();
    if (visited.find(t) == visited.end())
    {
      visited.insert(t);
      for (auto c : t)
      {
        to_visit.push_back(c);
      }

      if (t->is_symbolic_const())
      {
        num_consts++;
        cout << "checking " << t << endl;
        assert(timed_set.find(t) != timed_set.end());
      }
    }
  }
  assert(num_consts == timed_set.size());

  return 0;
}
