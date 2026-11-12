/*!
 * \file z3_factory.cpp
 * \brief Factory for creating a Z3 SmtSolver
 * \author Lindsey Stuntz
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/z3_factory.h"

#include <memory>

#include "smt-switch/logging_solver.h"
#include "smt-switch/z3_solver.h"

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
