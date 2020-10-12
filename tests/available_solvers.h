/*********************                                                        */
/*! \file available_solvers.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Convenience functions for testing. Collects the available solvers
**        and has maps for tagging supported features and filtering solvers
**        by feature.
**/

#pragma once

#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "smt_defs.h"
#include "solver_enums.h"

namespace smt_tests {

struct SolverConfiguration
{
  smt::SolverEnum solver_enum;
  bool is_logging_solver;
};

/** Creates an SmtSolver of the provided type */
smt::SmtSolver create_solver(SolverConfiguration sc);

/** Creates an interpolating SmtSolver of the provided type */
smt::SmtSolver create_interpolating_solver(SolverConfiguration sc);


// collect all the available solvers
std::vector<smt::SolverEnum> available_solver_enums();

// collect all the available solvers
std::vector<SolverConfiguration> available_solver_configurations();

// collect all the available interpolating solvers
std::vector<smt::SolverEnum> available_interpolator_enums();

// collect all the available interpolating solvers
std::vector<SolverConfiguration> available_interpolator_configurations();

/** Filter the available solvers by a set of attributes
 * @return all available solvers that have *all* the attributes
 */
std::vector<smt::SolverEnum> filter_solver_enums(
    const std::unordered_set<smt::SolverAttribute> attributes);

/** Filter the available solvers by a set of attributes
 * @return all available solvers that have *all* the attributes
 */
std::vector<SolverConfiguration> filter_solver_configurations(
    const std::unordered_set<smt::SolverAttribute> attributes);

}  // namespace smt_tests
