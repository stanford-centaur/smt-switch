#include "smt_defs.h"

namespace smt {
  class MsatSolverFactory
  {
  public:
    static SmtSolver create();
  };
}  // namespace smt
