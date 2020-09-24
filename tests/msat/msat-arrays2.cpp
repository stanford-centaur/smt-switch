/*********************                                                        */
/*! \file msat-arrays2.cpp
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
  s->set_opt("produce-models", "true");
  Sort bvsort4 = s->make_sort(BV, 4);
  Sort bvsort8 = s->make_sort(BV, 8);
  Sort array4_8 = s->make_sort(ARRAY, bvsort4, bvsort8);
  Term x = s->make_symbol("x", bvsort4);
  Term elem = s->make_symbol("elem", bvsort8);
  Term mem = s->make_symbol("mem", array4_8);

  Term new_array = s->make_term(Store, mem, x, elem);
  assert(new_array->get_op() == Store);

  for (auto c : new_array)
  {
    cout << c << endl;
  }

  return 0;
}
