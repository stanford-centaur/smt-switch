#include "yices2_factory.h"

#include "yices2_solver.h"

#include "logging_solver.h"

namespace smt {

bool initialized = false;

/* Yices2SolverFactory implementation with logging */
SmtSolver Yices2SolverFactory::create(bool logging)
{
  // Must initialize only once.
  // Different instances of the solver will have
  // different contexts.
  if (!initialized)
  {
    yices_init();
    initialized = true;
  }

  SmtSolver solver = std::make_shared<Yices2Solver>();
  if (logging)
  {
    solver = std::make_shared<LoggingSolver>(solver);
  }
  return solver;
}
/* end Yices2SolverFactory logging implementation */

}  // namespace smt
