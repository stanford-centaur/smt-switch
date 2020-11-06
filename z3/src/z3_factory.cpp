/*********************                                                        */
/*! \file z3_factory.cpp
** \verbatim
** Top contributors (to current version):
**   Lindsey Stuntz
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

/* Z3SolverFactory implementation with logging */
SmtSolver Z3SolverFactory::create(bool logging)
{
  SmtSolver solver = std::make_shared<Z3Solver>();
   if (logging)
   {
     solver = std::make_shared<LoggingSolver>(solver);
   }
  return solver;
}
/* end Z3SolverFactory implementation */

}  // namespace smt
