#include "smt_defs.h"

namespace smt {
  class Z3SolverFactory
  {
  public:
    static SmtSolver create();
  };
}  // namespace smt
