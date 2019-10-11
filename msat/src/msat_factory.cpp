#include "msat_factory.h"

#include "msat_solver.h"

namespace smt {

/* MsatSolverFactory implementation */

SmtSolver MsatSolverFactory::create()
{
  MsatSolver * ms = new MsatSolver();
  ms->setup_env();
  std::unique_ptr<MsatSolver> s(ms);
  return s;
}

SmtSolver MsatSolverFactory::create_interpolating_solver()
{
  MsatInterpolatingSolver * mis = new MsatInterpolatingSolver();
  mis->setup_env();
  std::unique_ptr<MsatInterpolatingSolver> s(mis);
  return s;
}

/* end MsatSolverFactory implementation */

}  // namespace smt
