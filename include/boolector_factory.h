#include "smt_defs.h"

namespace smt {
class BoolectorSolverFactory
{
 public:
  static SmtSolver create();
};
}  // namespace smt
