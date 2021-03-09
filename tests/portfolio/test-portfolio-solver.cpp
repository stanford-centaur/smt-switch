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
#include "portfolio_solver.h"
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
  solvers.push_back(s6);
  solvers.push_back(s8);
  solvers.push_back(s1);
  solvers.push_back(s3);
  solvers.push_back(s9);
  solvers.push_back(s7);
  solvers.push_back(s2);
  solvers.push_back(s4);
  solvers.push_back(s5);

  PortfolioSolver p;
  smt::Result res = p.portfolio_solve(solvers, test_term);
  cout << "portfolio_solve " << res.is_sat() << endl;

  assert(res.is_sat());

  SmtSolver s1_2 = MsatSolverFactory::create(false);
  SmtSolver s2_2 = MsatSolverFactory::create(false);
  SmtSolver s3_2 = MsatSolverFactory::create(false);
  SmtSolver s4_2 = BoolectorSolverFactory::create(false);
  SmtSolver s5_2 = BoolectorSolverFactory::create(false);
  SmtSolver s6_2 = Yices2SolverFactory::create(true);
  SmtSolver s7_2 = CVC4SolverFactory::create(false);
  SmtSolver s8_2 = CVC4SolverFactory::create(false);
  SmtSolver s9_2 = Yices2SolverFactory::create(true);
  vector<SmtSolver> solvers2;
  solvers2.push_back(s6_2);
  solvers2.push_back(s8_2);
  solvers2.push_back(s1_2);
  solvers2.push_back(s3_2);
  solvers2.push_back(s9_2);
  solvers2.push_back(s7_2);
  solvers2.push_back(s2_2);
  solvers2.push_back(s4_2);
  solvers2.push_back(s5_2);
  PortfolioSolver p2;
  smt::Result res2 = p2.portfolio_solve(solvers2, test_term);
  cout << "portfolio_solve2 " << res2.is_sat() << endl;

  return 0;
}
