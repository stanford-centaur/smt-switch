/*!
 * \file yices2_factory.h
 * \brief Factory for creating a Yices2 SmtSolver
 * \author Amalee Wilson
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_YICES2_FACTORY_H
#define SMT_SWITCH_YICES2_FACTORY_H

#include "smt-switch/smt_defs.h"

namespace smt {
class Yices2SolverFactory
{
 public:
  /** Create a Yices2 SmtSolver
   *  @param logging if true creates a LoggingSolver wrapper
   *         around the solver that keeps a shadow DAG at
   *         the smt-switch level.
   *         For yices2, term traversal works without it,
   *         but reads back Yices' own representation, so
   *         enable logging if you want to get back the
   *         exact term you created.
   *  @return a Yices2 SmtSolver
   */
  static SmtSolver create(bool logging);

  /** Create a Yices2 interpolating solver; see Yices2Interpolator
   *  for the theories it interpolates over.
   *  @return a Yices2 interpolating solver
   *  @throws NotImplementedException if this Yices2 was built without
   *          MCSAT, which interpolation needs and which Yices2 has only
   *          when built against LibPoly and CUDD
   */
  static SmtInterpolator create_interpolator();

  /** As create_interpolator */
  [[deprecated("use create_interpolator")]] static SmtInterpolator
  create_interpolating_solver();
};
}  // namespace smt

#endif  // SMT_SWITCH_YICES2_FACTORY_H
