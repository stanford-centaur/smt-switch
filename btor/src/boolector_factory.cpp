/*********************                                                        */
/*! \file boolector_factory.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Factory for creating a Boolector SmtSolver
**
**
**/

#include "boolector_factory.h"
#include "boolector_solver.h"
#include "logging_solver.h"

namespace smt {

/* BoolectorSolverFactory implementation */
SmtSolver BoolectorSolverFactory::create(bool logging)
{
  SmtSolver solver = std::make_shared<BoolectorSolver>();
  if (logging)
  {
    solver = std::make_shared<LoggingSolver>(solver);
  }
  return solver;
}

/* end BoolectorSolverFactory implementation */

}  // namespace smt
