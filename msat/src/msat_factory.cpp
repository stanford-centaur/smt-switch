/*!
 * \file msat_factory.cpp
 * \brief Factory for creating a MathSAT SmtSolver
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/msat_factory.h"

#include <memory>

#include "smt-switch/logging_solver.h"
#include "smt-switch/msat_solver.h"

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

SmtInterpolator MsatSolverFactory::create_interpolating_solver()
{
  MsatInterpolatingSolver * ps = new MsatInterpolatingSolver();
  std::shared_ptr<MsatInterpolatingSolver> s(ps);
  return s;
}

/* end MsatSolverFactory implementation */

}  // namespace smt
