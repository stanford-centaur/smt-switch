/*********************                                                        */
/*! \file portfolio_solver.h
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2021 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Header for a portfolio solving function that takes a vector
**        of solvers and a term, and returns check_sat from the first solver
**        that finishes.
**/
#pragma once

#include <vector>

#include "result.h"
#include "smt_defs.h"

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
