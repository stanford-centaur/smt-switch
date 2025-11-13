#pragma once

#include "smt_defs.h"

namespace smt {
class Z3SolverFactory
{
 public:
  /** Create a Z3 SmtSolver
   *  @param logging if true creates a LoggingSolver wrapper
   *         around the solver that keeps a shadow DAG at
   *         the smt-switch level.
   *  @return a Z3 SmtSolver
   */
  static SmtSolver create(bool logging);
};
}  // namespace smt
