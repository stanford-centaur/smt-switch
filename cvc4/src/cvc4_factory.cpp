/*********************                                                        */
/*! \file cvc4_factory.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Factory for creating a CVC4 SmtSolver
**
**
**/

#include "cvc4_factory.h"
#include "cvc4_solver.h"

#include "logging_solver.h"
#include "printing_solver.h"

namespace smt
{

/* CVC4SolverFactory implementation */
SmtSolver CVC4SolverFactory::create(bool logging)
{
  SmtSolver solver = std::make_shared<CVC4Solver>();
  if (logging)
  {
    solver = std::make_shared<LoggingSolver>(solver);
  }
  return solver;
}

/* end CVC4SolverFactory implementation */

} // namespace smt
