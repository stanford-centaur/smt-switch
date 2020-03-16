#include "cvc4_factory.h"

#include "cvc4_solver.h"

namespace smt
{

/* CVC4SolverFactory implementation */
SmtSolver CVC4SolverFactory::create()
{
  return std::make_shared<CVC4Solver>();
}
/* end CVC4SolverFactory implementation */

} // namespace smt
