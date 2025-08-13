/*********************                                                        */
/*! \file bzla-interpolants.cpp
** \verbatim
** Top contributors (to current version):
**   Po-Chun Chien
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
#include "bitwuzla_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/bitwuzla_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = BitwuzlaSolverFactory::create_interpolating_solver();
  Sort bv8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bv8);
  Term y = s->make_symbol("y", bv8);
  Term z = s->make_symbol("z", bv8);

  try
  {
    s->assert_formula(s->make_term(Equal, x, s->make_term(0, bv8)));
  }
  catch (IncorrectUsageException & e)
  {
    cout << e.what() << endl;
  }

  Term A =
      s->make_term(And, s->make_term(BVUlt, x, y), s->make_term(BVUlt, y, z));
  Term B = s->make_term(BVUgt, x, z);
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

  s->reset_assertions();

  // try getting a second interpolant with different A and B
  A = s->make_term(And, s->make_term(BVUgt, x, y), s->make_term(BVUgt, y, z));
  B = s->make_term(BVUlt, x, z);
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
  r = s->get_interpolant(A, s->make_term(BVUgt, x, z), I);
  assert(r.is_sat());

  return 0;
}
