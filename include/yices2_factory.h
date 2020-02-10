#include "smt_defs.h"

namespace smt {
  class Yices2SolverFactory
  {
  public:
    static SmtSolver create();
  };
}  // namespace smt
