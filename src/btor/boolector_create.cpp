#include "boolector_create.h"

#include "boolector_solver.h"

namespace smt {

/* BoolectorSolverFactory implementation */
SmtSolver BoolectorSolverFactory::create()
{
  return std::make_unique<BoolectorSolver>();
}
/* end BoolectorSolverFactory implementation */

}  // namespace smt
