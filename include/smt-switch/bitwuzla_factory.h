/*!
 * \file bitwuzla_factory.h
 * \brief Factory for creating a Bitwuzla SmtSolver
 * \author Makai Mann
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_BITWUZLA_FACTORY_H
#define SMT_SWITCH_BITWUZLA_FACTORY_H

#include "smt-switch/smt_defs.h"

namespace smt {
class BitwuzlaSolverFactory
{
 public:
  /** Create a bitwuzla SmtSolver
   *  @param logging if true creates a LoggingSolver wrapper
   *         around the solver that keeps a shadow DAG at
   *         the smt-switch level.
   *         For bitwuzla this should not be needed: it has a
   *         distinct Bool sort, so unlike Boolector it does not
   *         alias Bool with a width one bit-vector.
   *  @return a Bitwuzla SmtSolver
   */
  static SmtSolver create(bool logging);

  /** Create an interpolating Bitwuzla solver
   *  @return an interpolating Bitwuzla SmtInterpolator
   */
  static SmtInterpolator create_interpolator();

  /** As create_interpolator */
  [[deprecated("use create_interpolator")]] static SmtInterpolator
  create_interpolating_solver();
};
}  // namespace smt

#endif  // SMT_SWITCH_BITWUZLA_FACTORY_H
