#include "yices2_factory.h"

#include "yices2_solver.h"

namespace smt {

bool initialized = false;

/* Yices2SolverFactory implementation */
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

  return std::make_unique<Yices2Solver>();
}
/* end Yices2SolverFactory implementation */

}  // namespace smt
