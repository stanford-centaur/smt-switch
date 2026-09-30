/*********************                                                        */
/*! \file bitwuzla_factory.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Factory for creating a Bitwuzla SmtSolver
**
**
**/

#pragma once

#include "smt_defs.h"

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

  /** Create an interpolating Bitwuzla SmtSolver
   *  @return an interpolating Bitwuzla SmtSolver
   */
  static SmtSolver create_interpolating_solver();
};
}  // namespace smt
