#include "boolector_factory.h"
#include "boolector_solver.h"
#include "logging_solver.h"

namespace smt {

/* BoolectorSolverFactory implementation */
SmtSolver BoolectorSolverFactory::create()
{
  return std::make_shared<LoggingSolver>(create_lite_solver());
}

SmtSolver BoolectorSolverFactory::create_lite_solver()
{
  return std::make_shared<BoolectorSolver>();
}

/* end BoolectorSolverFactory implementation */

}  // namespace smt
