/*********************                                                        */
/*! \file boolector_factory.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Factory for creating a Boolector SmtSolver
**
**
**/

#include "smt_defs.h"

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
