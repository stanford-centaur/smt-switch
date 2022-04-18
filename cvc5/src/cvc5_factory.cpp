/*********************                                                        */
/*! \file cvc5_factory.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Factory for creating a cvc5 SmtSolver
**
**
**/

#include "cvc5_factory.h"

#include "cvc5_solver.h"
#include "logging_solver.h"

namespace smt {

/* Cvc5SolverFactory implementation */
SmtSolver Cvc5SolverFactory::create(bool logging)
{
  SmtSolver solver = std::make_shared<Cvc5Solver>();
  if (logging)
  {
    solver = std::make_shared<LoggingSolver>(solver);
  }
  return solver;
}

SmtSolver Cvc5SolverFactory::create_interpolating_solver()
{
  SmtSolver solver = std::make_shared<cvc5InterpolatingSolver>();
  /*
   * Enable interpolant generation.
   * */
  solver->set_opt("produce-interpolants", "true");
  solver->set_opt("incremental", "false");
  return solver;
}
/* end Cvc5SolverFactory implementation */

}  // namespace smt
