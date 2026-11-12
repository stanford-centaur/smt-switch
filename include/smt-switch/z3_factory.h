/*!
 * \file z3_factory.h
 * \brief Factory for creating a Z3 SmtSolver
 * \author Lindsey Stuntz
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_Z3_FACTORY_H
#define SMT_SWITCH_Z3_FACTORY_H

#include "smt-switch/smt_defs.h"

namespace smt {
class Z3SolverFactory
{
 public:
  /** Create a Z3 SmtSolver
   *  @param logging if true creates a LoggingSolver wrapper
   *         around the solver that keeps a shadow DAG at
   *         the smt-switch level.
   *  @return a Z3 SmtSolver
   */
  static SmtSolver create(bool logging);
};
}  // namespace smt

#endif  // SMT_SWITCH_Z3_FACTORY_H
