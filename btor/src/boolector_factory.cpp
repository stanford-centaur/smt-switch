#include "boolector_factory.h"
#include "boolector_solver.h"
#include "logging_solver.h"

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

}  // namespace smt
