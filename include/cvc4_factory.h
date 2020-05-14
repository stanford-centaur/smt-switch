#include "smt_defs.h"

namespace smt {
  class CVC4SolverFactory
  {
  public:
    /** Create a CVC4 SmtSolver
     *  @param logging if true creates a LoggingSolver wrapper
     *         around the solver that keeps a shadow DAG at
     *         the smt-switch level.
     *         For CVC4 this should never be necessary because
     *         the CVC4 API does not alias any sorts or
     *         perform on-the-fly rewriting.
     *  @return a CVC4 SmtSolver
     */
    static SmtSolver create(bool logging);
  };
}  // namespace smt
