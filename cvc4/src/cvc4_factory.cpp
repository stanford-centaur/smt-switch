#include "cvc4_factory.h"
#include "cvc4_solver.h"

#include "logging_solver.h"

namespace smt
{

/* CVC4SolverFactory implementation */
SmtSolver CVC4SolverFactory::create(bool logging)
{
  SmtSolver solver = std::make_shared<CVC4Solver>();
  if (logging)
  {
    solver = std::make_shared<LoggingSolver>(solver);
  }
  return solver;
}
/* end CVC4SolverFactory implementation */

} // namespace smt
