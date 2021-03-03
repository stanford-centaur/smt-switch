/*********************                                                        */
/*! \file test-generic-solver.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
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

#include <array>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include "assert.h"

#include "msat_factory.h"
#include "boolector_factory.h"
#include "portfolio_solver.h"
#include "smt.h"
#include "test-utils.h"

using namespace smt;
using namespace std;


int main() {
  cout << "testing portfolio solver" << endl; 
  SmtSolver s = MsatSolverFactory::create(false);
  s->set_opt("produce-models", "true");
  Sort bvsort32 = s->make_sort(BV, 32);
  Sort array32_32 = s->make_sort(ARRAY, bvsort32, bvsort32);
  Term x = s->make_symbol("x", bvsort32);
  Term y = s->make_symbol("y", bvsort32);
  Term arr = s->make_symbol("arr", array32_32);

  cout << "Sorts:" << endl;
  cout << "\tbvsort32 : " << bvsort32 << endl;
  cout << "\tarray32_32 : " << array32_32 << endl;

  Term test_term = s->make_term(Not,
                   s->make_term(Implies,
                                s->make_term(Equal, x, y),
                                s->make_term(Equal,
                                             s->make_term(Select, arr, x),
                                             s->make_term(Select, arr, y))));

  SmtSolver s1 = MsatSolverFactory::create(false);
  SmtSolver s2 = MsatSolverFactory::create(false);
  SmtSolver s3 = MsatSolverFactory::create(false);
  SmtSolver s4 = BoolectorSolverFactory::create(false);
  SmtSolver s5 = BoolectorSolverFactory::create(false);
  vector<SmtSolver> solvers;
  s1->set_opt("produce-models", "true");
  s2->set_opt("produce-models", "true");
  solvers.push_back(s1);
  solvers.push_back(s2);
  solvers.push_back(s3);
  solvers.push_back(s4);
  solvers.push_back(s5);
  
  cout << "portfolio_solve " << portfolio_solve(s, solvers, test_term) << endl;

  // s->assert_formula(test_term);
  assert(true);

  return 0;
}


