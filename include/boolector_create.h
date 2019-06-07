#include "smt.h"

namespace smt {
class BoolectorSolverFactory
{
 public:
  static SmtSolver create();
};
}  // namespace smt
