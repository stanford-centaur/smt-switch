/*********************                                                        */
/*! \file cvc4-interpolants.cpp
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
#include "assert.h"

#include "cvc4_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/cvc4_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = CVC4SolverFactory::create(false);
  s->set_opt("produce-interpols", "conclusion");
  s->set_opt("sygus-active-gen", "enum");
  Sort intsort = s->make_sort(INT);

  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  try
  {
    // x=0
    s->assert_formula(s->make_term(Equal, x, s->make_term(0, intsort)));
  }
  catch (IncorrectUsageException & e)
  {
    cout << e.what() << endl;
  }
  
  // x<y /\ y<z
  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  // x<z
  Term B = s->make_term(Gt, x, z);
  Term I;
  bool got_interpolant = s->get_interpolant(A, B, I);

  if (got_interpolant)
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
  s->reset_assertions();
  got_interpolant = s->get_interpolant(A, B, I);

  if (got_interpolant)
  {
    cout << "Found interpolant: " << I << endl;
  }
  else
  {
    cout << "Didn't find an interpolant..." << endl;
    assert(false);
  }

  // now try a satisfiable formula
  got_interpolant = s->get_interpolant(A, s->make_term(Gt, x, z), I);
  assert(!got_interpolant);

  return 0;
}
