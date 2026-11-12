/*********************                                                        */
/*! \file yices2_factory.h
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Factory for creating a Yices2 SmtSolver
**
**
**/
#ifndef SMT_SWITCH_YICES2_FACTORY_H
#define SMT_SWITCH_YICES2_FACTORY_H

#include "smt_defs.h"

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

  /** Create a Yices2 interpolating solver; see Yices2InterpolatingSolver
   *  for the theories it interpolates over.
   *  @return a Yices2 interpolating solver
   *  @throws NotImplementedException if this Yices2 was built without
   *          MCSAT, which interpolation needs and which Yices2 has only
   *          when built against LibPoly and CUDD
   */
  static SmtInterpolator create_interpolating_solver();
};
}  // namespace smt

#endif  // SMT_SWITCH_YICES2_FACTORY_H
