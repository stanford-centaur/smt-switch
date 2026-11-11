/*!
 * \file cvc5_factory.cpp
 * \brief Factory for creating a cvc5 SmtSolver
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/cvc5_factory.h"

#include <memory>

#include "smt-switch/cvc5_interpolator.h"
#include "smt-switch/cvc5_solver.h"
#include "smt-switch/logging_solver.h"

namespace smt {

/* Cvc5SolverFactory implementation */
SmtSolver Cvc5SolverFactory::create(bool logging)
{
  SmtSolver solver = std::make_shared<Cvc5Solver>();
  if (logging)
  {
    solver = std::make_shared<LoggingSolver>(solver);
  }
  return solver;
}

SmtInterpolator Cvc5SolverFactory::create_interpolator()
{
  return std::make_shared<Cvc5Interpolator>();
}

SmtInterpolator Cvc5SolverFactory::create_interpolating_solver()
{
  return create_interpolator();
}
/* end Cvc5SolverFactory implementation */

}  // namespace smt
