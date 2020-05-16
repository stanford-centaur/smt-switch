#include "msat_factory.h"
#include "msat_solver.h"

#include "logging_solver.h"

namespace smt {

/* MsatSolverFactory implementation */

SmtSolver MsatSolverFactory::create(bool logging)
{
  MsatSolver * ms = new MsatSolver();
  ms->setup_env();
  SmtSolver solver(ms);
  if (logging)
  {
    solver = std::make_shared<LoggingSolver>(solver);
  }
  return solver;
}

SmtSolver MsatSolverFactory::create_interpolating_solver()
{
  MsatInterpolatingSolver * mis = new MsatInterpolatingSolver();
  mis->setup_env();
  std::shared_ptr<MsatInterpolatingSolver> s(mis);
  return s;
}

/* end MsatSolverFactory implementation */

}  // namespace smt
