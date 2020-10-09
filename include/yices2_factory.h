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

#pragma once

#include "smt_defs.h"

namespace smt {
  class Yices2SolverFactory
  {
  public:
    /** Create a Yices2 SmtSolver
     *  @param logging if true creates a LoggingSolver wrapper
     *         around the solver that keeps a shadow DAG at
     *         the smt-switch level.
     *         For yices2, logging is *required* if you want
     *         to traverse terms.
     *  @return a Yices2 SmtSolver
     */
    static SmtSolver create(bool logging);
  };
}  // namespace smt
