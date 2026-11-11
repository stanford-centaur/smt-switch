/*!
 * \file cvc5_factory.h
 * \brief Factory for creating a cvc5 SmtSolver
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_CVC5_FACTORY_H
#define SMT_SWITCH_CVC5_FACTORY_H

#include "smt-switch/smt_defs.h"

namespace smt {
class Cvc5SolverFactory
{
 public:
  /** Create a cvc5 SmtSolver
   *  @param logging if true creates a LoggingSolver wrapper
   *         around the solver that keeps a shadow DAG at
   *         the smt-switch level.
   *         For cvc5 this should never be necessary because
   *         the cvc5 API does not alias any sorts or
   *         perform on-the-fly rewriting.
   *  @return a cvc5 SmtSolver
   */
  static SmtSolver create(bool logging);

  /** Create an interpolating cvc5 solver
   *  @return an interpolating cvc5 SmtInterpolator
   */
  static SmtInterpolator create_interpolator();

  /** As create_interpolator */
  [[deprecated("use create_interpolator")]] static SmtInterpolator
  create_interpolating_solver();
};
}  // namespace smt

#endif  // SMT_SWITCH_CVC5_FACTORY_H
