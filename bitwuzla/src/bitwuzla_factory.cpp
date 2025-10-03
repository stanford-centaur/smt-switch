/*********************                                                        */
/*! \file bitwuzla_factory.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Factory for creating a Bitwuzla SmtSolver
**
**
**/

#include "bitwuzla_factory.h"

#include <memory>

#include "bitwuzla_solver.h"
#include "logging_solver.h"
#include "smt_defs.h"

namespace smt {

/* BitwuzlaSolverFactory implementation */
SmtSolver BitwuzlaSolverFactory::create(bool logging)
{
  SmtSolver solver = std::make_shared<BzlaSolver>();
  if (logging)
  {
    solver = std::make_shared<LoggingSolver>(solver);
  }
  return solver;
}

SmtSolver BitwuzlaSolverFactory::create_interpolating_solver()
{
  return std::make_shared<BzlaInterpolatingSolver>();
}

/* end BitwuzlaSolverFactory implementation */

}  // namespace smt
