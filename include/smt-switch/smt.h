/*!
 * \file smt.h
 * \brief The main include file for the smt-switch abstract interface
 * \author Makai Mann
 * \author Clark Barrett
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_SMT_H
#define SMT_SWITCH_SMT_H

#ifdef SMT_SWITCH_INTERNAL
#error "smt.h is for external users; include the specific headers instead"
#endif

// Abstract datatype interface.
#include "smt-switch/datatype.h"  // IWYU pragma: export

// Exceptions used by SMT API.
#include "smt-switch/exceptions.h"  // IWYU pragma: export

// Interpolating solver interface.
#include "smt-switch/interpolator.h"  // IWYU pragma: export

// SMT-LIB Sort and Function operators.
#include "smt-switch/ops.h"  // IWYU pragma: export

// Results of satisfiability checks.
#include "smt-switch/result.h"  // IWYU pragma: export

// Class and smart pointer definitions.
#include "smt-switch/smt_defs.h"  // IWYU pragma: export

// Main solver interface.
#include "smt-switch/solver.h"  // IWYU pragma: export

// Solver enums for identifying solver
#include "smt-switch/solver_enums.h"  // IWYU pragma: export

// Abstract sort interface.
#include "smt-switch/sort.h"  // IWYU pragma: export

// Abstract term interface.
#include "smt-switch/term.h"  // IWYU pragma: export

// Term and sort building interface, shared by solvers and interpolators.
#include "smt-switch/term_builder.h"  // IWYU pragma: export

// Transfer terms between solvers.
#include "smt-switch/term_translator.h"  // IWYU pragma: export

#endif  // SMT_SWITCH_SMT_H
