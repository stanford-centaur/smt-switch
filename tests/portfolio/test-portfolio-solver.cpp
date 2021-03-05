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

#include "assert.h"
#include "boolector_factory.h"
#include "cvc4_factory.h"
#include "msat_factory.h"
#include "portfolio_solve.h"
#include "yices2_factory.h"

using namespace smt;
using namespace std;

int main()
{
  cout << "testing portfolio solver" << endl;
  SmtSolver s = MsatSolverFactory::create(false);
  s->set_opt("produce-models", "true");
  Sort intsort = s->make_sort(BV, 10);

  int pg = 300;

  vector<Term> nts;
  for (int i = 0; i < pg; ++i)
  {
    Term x = s->make_symbol("x" + to_string(i), intsort);
    nts.push_back(x);
  }

  Term ten24 = s->make_term(256, intsort);
  vector<Term> neqs;
  for (int i = 0; i < pg; ++i)
  {
    for (int j = 0; j < pg; ++j)
    {
      if (i != j)
      {
        Term x = s->make_term(Not, s->make_term(Equal, nts[i], nts[j]));
        neqs.push_back(x);
      }
    }
    Term y = s->make_term(BVSle, nts[i], ten24);
    neqs.push_back(y);
  }

  Term test_term = s->make_term(Equal, neqs[0], neqs[0]);
  for (Term t : neqs)
  {
    test_term = s->make_term(And, t, test_term);
  }

  SmtSolver s1 = MsatSolverFactory::create(false);
  SmtSolver s2 = MsatSolverFactory::create(false);
  SmtSolver s3 = MsatSolverFactory::create(false);
  SmtSolver s4 = BoolectorSolverFactory::create(false);
  SmtSolver s5 = BoolectorSolverFactory::create(false);
  SmtSolver s6 = Yices2SolverFactory::create(true);
  SmtSolver s7 = CVC4SolverFactory::create(false);
  SmtSolver s8 = CVC4SolverFactory::create(false);
  SmtSolver s9 = Yices2SolverFactory::create(true);
  vector<SmtSolver> solvers;
  s1->set_opt("produce-models", "true");
  s2->set_opt("produce-models", "true");
  solvers.push_back(s6);
  solvers.push_back(s8);
  solvers.push_back(s1);
  solvers.push_back(s3);
  solvers.push_back(s9);
  solvers.push_back(s7);
  solvers.push_back(s2);
  solvers.push_back(s4);
  solvers.push_back(s5);

  bool is_sat = portfolio_solve(solvers, test_term);
  cout << "portfolio_solve " << is_sat << endl;

  assert(is_sat);

  return 0;
}
