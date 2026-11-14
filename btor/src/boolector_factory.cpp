/*!
 * \file boolector_factory.cpp
 * \brief Factory for creating a Boolector SmtSolver
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/boolector_factory.h"

#include <memory>

#include "smt-switch/boolector_solver.h"
#include "smt-switch/logging_solver.h"
#include "smt-switch/solver_factory.h"

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

const detail::BackendFactory detail::smt_switch_backend_btor = {
  &BoolectorSolverFactory::create, nullptr
};

}  // namespace smt
