#include "msat_factory.h"

#include "msat_solver.h"

namespace smt {

/* MsatSolverFactory implementation */
SmtSolver MsatSolverFactory::create() { return std::make_unique<MsatSolver>(); }
/* end MsatSolverFactory implementation */

}  // namespace smt
