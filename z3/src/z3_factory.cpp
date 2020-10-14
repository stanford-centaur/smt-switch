//#include "z3_factory.h"
//
//#include "z3_solver.h"
//
//namespace smt
//{
//
///* Z3SolverFactory implementation */
//SmtSolver Z3SolverFactory::create()
//{
//  return std::make_unique<Z3Solver>();
//}
///* end Z3SolverFactory implementation */
//
//} // namespace smt







#include "z3_factory.h"
#include "z3_solver.h"

#include "logging_solver.h"

namespace smt
{

/* Z3SolverFactory implementation */
SmtSolver Z3SolverFactory::create(bool logging)
{
  SmtSolver solver = std::make_shared<Z3Solver>();
  if (logging)
  {
    solver = std::make_shared<LoggingSolver>(solver);
  }
  return solver;
}
/* end Z3SolverFactory implementation */

} // namespace smt

