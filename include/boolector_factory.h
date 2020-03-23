#include "smt_defs.h"

namespace smt {
class BoolectorSolverFactory
{
 public:
  /** Create a boolector SmtSolver
   *  @return an SmtSolver
   */
  static SmtSolver create();

  /** Create a solver without a shadow DAG
   *  Some solvers do on-the-fly rewriting and/or
   *  alias sorts. Smt-switch provides a shadow
   *  DAG so that term traversal and translation
   *  is reliable.
   *  This function creates a "raw" solver without
   *  the extra logging at the smt-switch level
   *  @return an SmtSolver
   */
  static SmtSolver create_lite_solver();
};
}  // namespace smt
