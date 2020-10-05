#include "z3_factory.h"

#include "z3_solver.h"

namespace smt
{

/* Z3SolverFactory implementation */
SmtSolver Z3SolverFactory::create()
{
  return std::make_unique<Z3Solver>();
}
/* end Z3SolverFactory implementation */

} // namespace smt
