/*********************                                                        */
/*! \file cvc4_factory.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Factory for creating a CVC4 SmtSolver
**
**
**/

#pragma once

#include "smt_defs.h"

namespace smt {
  class CVC4SolverFactory
  {
  public:
    /** Create a CVC4 SmtSolver
     *  @param logging if true creates a LoggingSolver wrapper
     *         around the solver that keeps a shadow DAG at
     *         the smt-switch level.
     *         For CVC4 this should never be necessary because
     *         the CVC4 API does not alias any sorts or
     *         perform on-the-fly rewriting.
     *  @return a CVC4 SmtSolver
     */
    static SmtSolver create(bool logging);

    /** Create an interpolating CVC4 SmtSolver
     *  @return an interpolating CVC4 SmtSolver
     */
    static SmtSolver create_interpolating_solver();
  };
}  // namespace smt
