/*********************                                                        */
/*! \file msat-int-arithmetic.cpp
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

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = MsatSolverFactory::create(false);
  s->set_opt("produce-models", "true");
  s->set_logic("QF_LRA");
  Sort realsort = s->make_sort(REAL);

  smt::Sort sort_ = s->make_sort(smt::REAL);
  smt::Term b = s->make_symbol("b", s->make_sort(smt::BOOL));
  smt::Term v1 = s->make_term("0.0", sort_);
  assert(v1->get_sort()->get_sort_kind()
         == smt::INT);  // MathSAT stores 0.0 as INT
  smt::Term v2 = s->make_term("0.1", sort_);
  // The following expression is legal for MathSAT even though v1 is REAL and v2
  // is INT
  smt::Term f2 = s->make_term(smt::Ite, b, v1, v2);
  return 0;
}
