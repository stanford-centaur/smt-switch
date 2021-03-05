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

#include <condition_variable>
#include <mutex>
#include <thread>

#include "smt.h"

namespace smt {

/** Translate the term t to the solver s, and check_sat.
 *  @param s The solver to translate the term t to.
 *  @param t The term being translated to solver s.
 */
void run_solver(SmtSolver s, Term t);

/** Launch many solvers and return whether the term is satisfiable when one of
 *  them has finished.
 *  @param solvers The solvers to run.
 *  @param t The term to be checked.
 */
bool portfolio_solve(std::vector<SmtSolver> solvers, Term t);

}  // namespace smt
