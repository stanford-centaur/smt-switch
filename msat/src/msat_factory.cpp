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
#include "smt-switch/msat_interpolator.h"
#include "smt-switch/msat_solver.h"
#include "smt-switch/solver_factory.h"

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

SmtInterpolator MsatSolverFactory::create_interpolator()
{
  MsatInterpolator * ps = new MsatInterpolator();
  std::shared_ptr<MsatInterpolator> s(ps);
  return s;
}

SmtInterpolator MsatSolverFactory::create_interpolating_solver()
{
  return create_interpolator();
}

/* end MsatSolverFactory implementation */

const detail::BackendFactory detail::smt_switch_backend_msat = {
  &MsatSolverFactory::create, &MsatSolverFactory::create_interpolator
};

}  // namespace smt
