/*********************                                                        */
/*! \file z3_factory.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Factory for creating a Z3 SmtSolver
**
**
**/

#include "z3_factory.h"

#include "z3_solver.h"

#include "logging_solver.h"

namespace smt {

bool initialized = false;

/* Z3SolverFactory implementation with logging */
SmtSolver Z3SolverFactory::create(bool logging)
{
  // Must initialize only once.
  // Different instances of the solver will have
  // different contexts.
  // if (!initialized)
  // {
  //   yices_init();
  //   initialized = true;
  // }

  SmtSolver solver = std::make_shared<Z3Solver>();
  // if (logging)
  // {
  //   solver = std::make_shared<LoggingSolver>(solver);
  // }
  return solver;
}
/* end Z3SolverFactory logging implementation */

}  // namespace smt
