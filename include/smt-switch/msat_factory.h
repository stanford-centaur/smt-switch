/*!
 * \file msat_factory.h
 * \brief Factory for creating a MathSAT SmtSolver
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_MSAT_FACTORY_H
#define SMT_SWITCH_MSAT_FACTORY_H

#include "smt-switch/smt_defs.h"

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

  /** Create an interpolating MathSAT solver
   *  @return an interpolating MathSAT SmtInterpolator
   */
  static SmtInterpolator create_interpolating_solver();
};

}  // namespace smt

#endif  // SMT_SWITCH_MSAT_FACTORY_H
