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

// IWYU pragma: begin_exports

// Abstract datatype interface.
#include "smt-switch/datatype.h"

// Exceptions used by SMT API.
#include "smt-switch/exceptions.h"

// Interpolating solver interface.
#include "smt-switch/interpolator.h"

// SMT-LIB Sort and Function operators.
#include "smt-switch/ops.h"

// Results of satisfiability checks.
#include "smt-switch/result.h"

// Class and smart pointer definitions.
#include "smt-switch/smt_defs.h"

// Main solver interface.
#include "smt-switch/solver.h"

// Solver enums for identifying solver
#include "smt-switch/solver_enums.h"

// Abstract sort interface.
#include "smt-switch/sort.h"

// Abstract term interface.
#include "smt-switch/term.h"

// Term and sort building interface, shared by solvers and interpolators.
#include "smt-switch/term_builder.h"

// Transfer terms between solvers.
#include "smt-switch/term_translator.h"

// IWYU pragma: end_exports

#endif  // SMT_SWITCH_SMT_H
