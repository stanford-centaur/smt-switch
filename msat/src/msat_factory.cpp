/*********************                                                        */
/*! \file msat_factory.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Factory for creating a MathSAT SmtSolver
**
**
**/

#include "msat_factory.h"
#include "msat_solver.h"

#include "logging_solver.h"

namespace smt {

/* MsatSolverFactory implementation */

SmtSolver MsatSolverFactory::create(bool logging)
{
  MsatSolver * ms = new MsatSolver();
  SmtSolver solver(ms);
  if (logging)
  {
    solver = std::make_shared<LoggingSolver>(solver);
  }
  return solver;
}

SmtSolver MsatSolverFactory::create_interpolating_solver()
{
  MsatInterpolatingSolver * mis = new MsatInterpolatingSolver();
  std::shared_ptr<MsatInterpolatingSolver> s(mis);
  return s;
}

/* end MsatSolverFactory implementation */

}  // namespace smt
