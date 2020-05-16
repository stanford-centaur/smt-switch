#include "smt_defs.h"

namespace smt {
class BoolectorSolverFactory
{
 public:
  /** Create a boolector SmtSolver
   *  @param logging if true creates a LoggingSolver wrapper
   *         around the solver that keeps a shadow DAG at
   *         the smt-switch level.
   *         For boolector, this is not required but will
   *         but makes it easier to transfer terms to other
   *         solvers because it avoids the bool / width one
   *         bitvector sort aliasing
   *  @return a Boolector SmtSolver
   */
  static SmtSolver create(bool logging);
};
}  // namespace smt
