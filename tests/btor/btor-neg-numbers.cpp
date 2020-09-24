/*********************                                                        */
/*! \file btor-neg-numbers.cpp
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

#include "boolector_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/boolector_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = BoolectorSolverFactory::create(false);

  Sort bvsort8 = s->make_sort(BV, 8);

  Term four = s->make_term(4, bvsort8);
  Term neg_four = s->make_term(-4, bvsort8);

  assert(neg_four == s->make_term("-4", bvsort8));

  try
  {
    Term impossible = s->make_term("-129", bvsort8);
    assert(false);
  }
  catch (IncorrectUsageException & e)
  {
    cout << e.what() << endl;
  }

  s->assert_formula(
      s->make_term(Not,
                   s->make_term(Equal,
                                s->make_term(BVAdd, four, neg_four),
                                s->make_term(0, bvsort8))));
  Result r = s->check_sat();
  assert(r.is_unsat());

  return 0;
}
