/*********************                                                        */
/*! \file cvc5-data-structures.cpp
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
#include <string>

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
  unsigned int NUM_TERMS = 20;

  SmtSolver s = Cvc5SolverFactory::create(false);
  s->set_opt("produce-models", "true");
  Sort bvsort8 = s->make_sort(BV, 8);

  UnorderedTermSet uts;
  UnorderedTermMap utm;
  TermVec v;
  v.reserve(NUM_TERMS);
  Term x;
  Term y;
  for (size_t i = 0; i < NUM_TERMS; ++i)
  {
    x = s->make_symbol("x" + to_string(i), bvsort8);
    y = s->make_symbol("y" + to_string(i), bvsort8);
    v.push_back(x);
    uts.insert(x);
    utm[x] = y;
  }

  Term trailing = v[0];
  for (size_t i = 1; i < NUM_TERMS; ++i)
  {
    s->assert_formula(s->make_term(
        Equal, v[i], s->make_term(BVAdd, trailing, s->make_term(1, bvsort8))));
    trailing = v[i];
  }

  Term zero = s->make_term(0, bvsort8);
  cout << zero->to_string() << endl;

  assert(zero->is_value());
  assert(!v[0]->is_value());

  Term v0_eq_0 = s->make_term(Equal, v[0], zero);
  s->assert_formula(v0_eq_0);

  cout << "Children of term:" << endl;
  // Could use iterators directly:
  //   for (TermIter it = v0_eq_0->begin(); it != v0_eq_0->end(); ++it)
  // Or use a range-based loop
  for (auto c : v0_eq_0)
  {
    cout << "got: " << c << endl;
  }

  // just assign all ys to x counterparts
  for (auto it = uts.begin(); it != uts.end(); ++it)
  {
    x = *it;
    y = utm.at(*it);
    std::cout << "assert: " << x << " = " << y << std::endl;
    s->assert_formula(s->make_term(Equal, x, y));
  }

  bool res = s->check_sat().is_sat();
  assert(res);

  // can print variable names, but otherwise boolector doesn't maintain strings
  // for expressions
  cout << "Assignments:" << std::endl;
  for (size_t i = 0; i < NUM_TERMS; ++i)
  {
    cout << "\t " << v[i]->to_string() << " = " << s->get_value(v[i])->to_int()
         << endl;
    cout << "\t " << utm.at(v[i])->to_string() << " = "
         << s->get_value(utm.at(v[i]))->to_int() << endl;
  }

  // create sets of sorts
  UnorderedSortSet sset;
  Sort s0, s1, s2, s3;
  s0 = s->make_sort(BV, 1);
  s1 = s->make_sort(BV, 4);
  s2 = s->make_sort(BOOL);
  s3 = s->make_sort(BV, 5);
  sset.insert(s0);
  sset.insert(s1);
  sset.insert(s2);
  sset.insert(s3);

  cout << "sset size is: " << sset.size() << endl;
  assert(sset.size() == 4);

  return 0;
}
