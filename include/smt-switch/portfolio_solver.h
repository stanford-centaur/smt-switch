/*!
 * \file portfolio_solver.h
 * \brief Header for a portfolio solving function that takes a vector of solvers
 *        and a term, and returns check_sat from the first solver that finishes
 * \author Amalee Wilson
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_PORTFOLIO_SOLVER_H
#define SMT_SWITCH_PORTFOLIO_SOLVER_H

#include <vector>

#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"

namespace smt {

class PortfolioSolver
{
 public:
  PortfolioSolver(std::vector<SmtSolver> slvrs, Term trm);

  /** Checks the term with every solver at once, and returns the answer of
   *  whichever finishes first.
   *
   *  Each solver runs in a child process of its own, which is killed once
   *  another has answered. So the solvers passed in are left as they were:
   *  the term is asserted in the children's copies of them. A solver that
   *  throws or crashes only drops out. Should all of them, this throws an
   *  SmtException that says why each one failed.
   *
   *  The children are forked from the calling thread alone. Do not call this
   *  while another thread is using a solver, as a lock that thread holds
   *  would stay held in the children.
   */
  Result portfolio_solve();

 private:
  std::vector<SmtSolver> solvers;
  Term portfolio_term;
};
}  // namespace smt

#endif  // SMT_SWITCH_PORTFOLIO_SOLVER_H
