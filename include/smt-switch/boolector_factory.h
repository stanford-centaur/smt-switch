/*!
 * \file boolector_factory.h
 * \brief Factory for creating a Boolector SmtSolver
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_BOOLECTOR_FACTORY_H
#define SMT_SWITCH_BOOLECTOR_FACTORY_H

#include "smt-switch/smt_defs.h"

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

#endif  // SMT_SWITCH_BOOLECTOR_FACTORY_H
