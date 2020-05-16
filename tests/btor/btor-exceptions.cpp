/*********************                                                        */
/*! \file btor-exceptions.cpp
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
  s->set_opt("produce-models", "true");

  try
  {
    s->set_logic("QF_NIA");
  }
  catch (SmtException & e)
  {
    cout << e.what() << endl;
  }

  try
  {
    Sort intsort = s->make_sort(INT);
  }
  catch (SmtException & e)
  {
    cout << e.what() << endl;
  }

  Sort bvsort4 = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bvsort4);
  Term y = s->make_symbol("y", bvsort4);

  try
  {
    s->assert_formula(s->make_term(Ge, x, y));
  }
  catch (SmtException & e)
  {
    cout << e.what() << endl;
  }
  return 0;
}
