#include "smt_defs.h"

namespace smt {
  class MsatSolverFactory
  {
  public:
    static SmtSolver create();
    static SmtSolver create_interpolating_solver();
  };
}  // namespace smt
