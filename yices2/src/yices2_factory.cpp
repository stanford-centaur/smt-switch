/*********************                                                        */
/*! \file yices2_factory.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Factory for creating a Yices2 SmtSolver
**
**
**/

#include "smt-switch/yices2_factory.h"

#include <gmp.h>  // IWYU pragma: keep (required by yices.h)
#include <yices.h>

#include <memory>

#include "smt-switch/exceptions.h"
#include "smt-switch/logging_solver.h"
#include "smt-switch/yices2_interpolating_solver.h"
#include "smt-switch/yices2_solver.h"

namespace smt {

/* Yices2SolverFactory implementation with logging */
SmtSolver Yices2SolverFactory::create(bool logging)
{
  // Different instances of the solver will have
  // different contexts. Yices2 must be configured
  // with --enable-thread-safety in order for
  // multiple threads to manipulate different contexts.
  // https://github.com/SRI-CSL/yices2#support-for-thread-safety
  SmtSolver solver = std::make_shared<Yices2Solver>();
  if (logging)
  {
    solver = std::make_shared<LoggingSolver>(solver);
  }
  return solver;
}
/* end Yices2SolverFactory logging implementation */

SmtInterpolator Yices2SolverFactory::create_interpolating_solver()
{
  if (!yices_has_mcsat())
  {
    throw NotImplementedException(
        "This Yices2 was built without MCSAT, which interpolation needs");
  }
  return std::make_shared<Yices2InterpolatingSolver>();
}

}  // namespace smt
