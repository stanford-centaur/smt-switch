/*********************                                                        */
/*! \file msat-traversal.cpp
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
  Sort bvsort8 = s->make_sort(BV, 8);
  cout << "making x" << endl;
  Term x = s->make_symbol("x", bvsort8);
  cout << "making y" << endl;
  Term y = s->make_symbol("y", bvsort8);
  cout << "making z" << endl;
  Term z = s->make_symbol("z", bvsort8);

  // cout << "making a" << endl;
  // Term a = s->make_term(BVAdd, x, y);
  cout << "making constraint" << endl;
  // Term constraint = s->make_term(Equal, z, a);
  Term constraint = s->make_term(Equal, z, s->make_term(BVAdd, x, y));
  std::cout << "right after making constraint" << std::endl;
  s->assert_formula(constraint);

  for (auto c : constraint)
  {
    for (auto t : c)
    {
      cout << c->hash() << endl;
    }
  }

  // Identity traversal
  // UnorderedTermMap cache;
  // TermVec to_visit{constraint};
  // Term t;
  // while(to_visit.size())
  // {

  //   t = to_visit.back();
  //   to_visit.pop_back();

  //   cout << "in visitor with " << t << " and visited = ";

  //   if (cache.find(t) == cache.end())
  //   {
  //     cout << "0" << endl;
  //     to_visit.push_back(t);
  //     for (auto c : t)
  //     {
  //       to_visit.push_back(c);
  //     }
  //   }
  //   else
  //   {
  //     cout << "1" << endl;
  //     TermVec cached_children;
  //     for (auto c : t)
  //     {
  //       cached_children.push_back(cache.at(c));
  //     }

  //     if (cached_children.size())
  //     {
  //       // rebuild
  //       cache[t] = s->make_term(t->get_op(), cached_children);
  //     }
  //     else
  //     {
  //       cache[t] = t;
  //     }
  //   }
  // }

  return 0;
}
