/*!
 * \file yices2_factory.cpp
 * \brief Factory for creating a Yices2 SmtSolver
 * \author Amalee Wilson
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/yices2_factory.h"

#include <gmp.h>  // IWYU pragma: keep (required by yices.h)
#include <yices.h>

#include <memory>

#include "smt-switch/exceptions.h"
#include "smt-switch/logging_solver.h"
#include "smt-switch/solver_factory.h"
#include "smt-switch/yices2_interpolator.h"
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

SmtInterpolator Yices2SolverFactory::create_interpolator()
{
  if (!yices_has_mcsat())
  {
    throw NotImplementedException(
        "This Yices2 was built without MCSAT, which interpolation needs");
  }
  return std::make_shared<Yices2Interpolator>();
}

SmtInterpolator Yices2SolverFactory::create_interpolating_solver()
{
  return create_interpolator();
}

const detail::BackendFactory detail::smt_switch_backend_yices2 = {
  &Yices2SolverFactory::create, &Yices2SolverFactory::create_interpolator
};

}  // namespace smt
