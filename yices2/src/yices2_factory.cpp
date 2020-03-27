#include "yices2_factory.h"

#include "yices2_solver.h"

#include "logging_solver.h"

namespace smt {

bool initialized = false;

/* Yices2SolverFactory implementation with logging */
SmtSolver Yices2SolverFactory::create()
{
  // Must initialize only once.
  // Different instances of the solver will have
  // different contexts.
  if (!initialized)
  {
    yices_init();
    initialized = true;
  }

  return std::make_shared<LoggingSolver>(create_lite_solver());
}
/* end Yices2SolverFactory logging implementation */

/* Yices2SolverFactory implementation without logging */
SmtSolver Yices2SolverFactory::create_lite_solver()
{
  // Must initialize only once.
  // Different instances of the solver will have
  // different contexts.
  if (!initialized)
  {
    yices_init();
    initialized = true;
  }

  return std::make_shared<Yices2Solver>();
}
/* end Yices2SolverFactory lite (no logging) implementation */

}  // namespace smt
