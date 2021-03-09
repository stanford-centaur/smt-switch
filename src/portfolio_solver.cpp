/*********************                                                        */
/*! \file portfolio_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2021 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Implementation of a portfolio solving function that takes a vector
**        of solvers and a term, and returns check_sat from the first solver
**        that finishes.
**/

#include "portfolio_solver.h"

#include <unistd.h>
namespace smt {

PortfolioSolver::PortfolioSolver(std::vector<SmtSolver> slvrs, Term trm)
    : solvers(slvrs), portfolio_term(trm)
{
}
/** Translate the term t to the solver s, and check_sat.
 *  @param s The solver to translate the term t to.
 *  @param t The term being translated to solver s.
 */
void PortfolioSolver::run_solver(SmtSolver s)
{
  TermTranslator to_s(s);
  Term a = to_s.transfer_term(portfolio_term, smt::BOOL);
  s->assert_formula(a);
  result = s->check_sat();
  std::lock_guard<std::mutex> lk(m);
  a_solver_is_done = true;

  cv.notify_all();
}

/** Launch many solvers and return whether the term is satisfiable when one of
 *  them has finished.
 *  @param solvers The solvers to run.
 *  @param t The term to be checked.
 */
smt::Result PortfolioSolver::portfolio_solve()
{
  // We must maintain a vector of pthreads in order to stop the threads that are
  // still running once one of the solvers finish because pthreads is assumed to
  // be the underlying implementation.
  for (auto s : solvers)
  {
    // Start a thread, store its handle, and detach the thread because we are
    // not interested in waiting for all of them to finish.
    std::thread t1(&PortfolioSolver::run_solver, this, s);
    t1.detach();
  }

  // Wait until a solver is done to cancel the threads that are still running.
  std::unique_lock<std::mutex> lk(m);
  while (!a_solver_is_done) cv.wait(lk);

  return result;
}

}  // namespace smt
