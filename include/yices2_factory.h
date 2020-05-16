#include "smt_defs.h"

namespace smt {
  class Yices2SolverFactory
  {
  public:
    /** Create a Yices2 SmtSolver
     *  @param logging if true creates a LoggingSolver wrapper
     *         around the solver that keeps a shadow DAG at
     *         the smt-switch level.
     *         For yices2, logging is *required* if you want
     *         to traverse terms.
     *  @return a Yices2 SmtSolver
     */
    static SmtSolver create(bool logging);
  };
}  // namespace smt
