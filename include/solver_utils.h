/*********************                                                        */
/*! \file solver_utils.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Utility functions for solver implementations. Meant for internal
**        use only, not from the API.
**
**/
#pragma once

#include "smt.h"

namespace smt {

/** Create distinctness constraint for each unique pair
 *  @param terms the vector of terms to make distinct
 *  @return the distinctness constraint
 */
smt::Term make_distinct(const smt::AbsSmtSolver * solver,
                        const smt::TermVec & terms);

}  // namespace smt
