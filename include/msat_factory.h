/*********************                                                        */
/*! \file msat_factory.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Factory for creating a MathSAT SmtSolver
**
**
**/

#include "smt_defs.h"

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

    /** Create an interpolating MathSAT SmtSolver
     *  @return an interpolating MathSAT SmtSolver
     */
    static SmtSolver create_interpolating_solver();
  };
}  // namespace smt
