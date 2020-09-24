/*********************                                                        */
/*! \file msat-interpolants.cpp
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
  SmtSolver s = MsatSolverFactory::create_interpolating_solver();
  Sort intsort = s->make_sort(INT);

  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  try
  {
    s->assert_formula(s->make_term(Equal, x, s->make_term(0, intsort)));
  }
  catch (IncorrectUsageException & e)
  {
    cout << e.what() << endl;
  }

  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  Term B = s->make_term(Gt, x, z);
  Term I;
  Result r = s->get_interpolant(A, B, I);

  if (r.is_unsat())
  {
    cout << "Found interpolant: " << I << endl;
  }
  else
  {
    cout << "Didn't find an interpolant..." << endl;
    assert(false);
  }

  // try getting a second interpolant with different A and B
  A = s->make_term(And, s->make_term(Gt, x, y), s->make_term(Gt, y, z));
  B = s->make_term(Lt, x, z);
  r = s->get_interpolant(A, B, I);

  if (r.is_unsat())
  {
    cout << "Found interpolant: " << I << endl;
  }
  else
  {
    cout << "Didn't find an interpolant..." << endl;
    assert(false);
  }

  // now try a satisfiable formula
  r = s->get_interpolant(A, s->make_term(Gt, x, z), I);
  assert(r.is_sat());

  return 0;
}
