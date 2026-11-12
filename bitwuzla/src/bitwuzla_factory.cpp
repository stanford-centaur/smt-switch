/*!
 * \file bitwuzla_factory.cpp
 * \brief Factory for creating a Bitwuzla SmtSolver
 * \author Makai Mann
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/bitwuzla_factory.h"

#include <memory>

#include "smt-switch/bitwuzla_solver.h"
#include "smt-switch/logging_solver.h"
#include "smt-switch/smt_defs.h"

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

SmtInterpolator BitwuzlaSolverFactory::create_interpolating_solver()
{
  return std::make_shared<BzlaInterpolatingSolver>();
}

/* end BitwuzlaSolverFactory implementation */

}  // namespace smt
