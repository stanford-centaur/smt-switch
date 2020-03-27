#include "smt_defs.h"

namespace smt {
  class Yices2SolverFactory
  {
  public:
    static SmtSolver create();
    static SmtSolver create_lite_solver();
  };
}  // namespace smt
