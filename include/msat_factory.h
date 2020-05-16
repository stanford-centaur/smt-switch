#include "smt_defs.h"

namespace smt {
  class MsatSolverFactory
  {
  public:
      /** Create a MathSAT SmtSolver
       *  @param logging if true creates a LoggingSolver wrapper
       *         around the solver that keeps a shadow DAG at
       *         the smt-switch level.
       *         For MathSAT this should not be needed because
       *         it does not alias sorts. However, it does
       *         do some light rewriting on-the-fly, so if
       *         you want to guarantee that you get the exact
       *         term you created back from term traversal,
       *         please enable logging.
       *  @return a MathSAT SmtSolver
       */
    static SmtSolver create(bool logging);

    /** Create an interpolating MathSAT SmtSolver
     *  @return an interpolating MathSAT SmtSolver
     */
    static SmtSolver create_interpolating_solver();
  };
}  // namespace smt
