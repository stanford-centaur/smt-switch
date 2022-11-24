/*********************                                                        */
/*! \file solver_enums.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Enums for identifying SmtSolver objects
**
**
**/

#pragma once

#include <unordered_set>

namespace smt {
enum SolverEnum
{
  BTOR = 0,  // boolector
  BZLA,      // bitwuzla
  CVC5,      // cvc5
  MSAT,      // mathsat
  YICES2,    // yices2
  Z3,        // z3

  // interpolating solvers -- note these cannot be logging solvers
  // because the solver takes the initiative in creating the interpolant
  // so there's no way to keep a DAG at the smt-switch level
  MSAT_INTERPOLATOR,
  CVC5_INTERPOLATOR,
  GENERIC_SOLVER

  // TODO: when adding a new enum, also add to python interface in enums_dec.pxi
  // and enums_imp.pxi
};

enum SolverAttribute
{
  LOGGING = 0,
  // supports traversing terms with iteration
  TERMITER,
  // supports bit-vector theory
  THEORY_BV,
  // supports integer theory
  THEORY_INT,
  // supports real theory
  THEORY_REAL,
  // supports array models
  ARRAY_MODELS,
  // supports constant arrays
  CONSTARR,
  // supports transferring to different solvers with TermTranslator
  FULL_TRANSFER,
  // supports functions with boolean arguments
  // and arrays with boolean elements
  ARRAY_FUN_BOOLS,
  // unsat core support
  UNSAT_CORE,
  // supports datatype theory
  THEORY_DATATYPE,
  // supports quantifiers
  QUANTIFIERS,
  // supports zero arity uninterpreted sorts
  UNINTERP_SORT,
  // supports non-zero arity uninterpreted sorts
  PARAM_UNINTERP_SORT,
  // aliases booleans and bit-vectors of size one
  BOOL_BV1_ALIASING,
  // supports setting a time limit
  TIMELIMIT

  // TODO: when adding a new enum, also add to python interface in enums_dec.pxi
  // and enums_imp.pxi
};

/** Returns true iff the SolverEnum corresponds to an Interpolator
 *  @param se the solver enum to check
 *  @return true iff the se is a *_INTERPOLATOR enum
 */
bool is_interpolator_solver_enum(SolverEnum se);

bool solver_has_attribute(SolverEnum se, SolverAttribute sa);

std::unordered_set<SolverAttribute> get_solver_attributes(SolverEnum se);

std::ostream & operator<<(std::ostream & o, SolverEnum e);

std::string to_string(SolverEnum e);

std::ostream & operator<<(std::ostream & o, SolverAttribute sa);

std::string to_string(SolverAttribute a);

}  // namespace smt

// define hash for older compilers
namespace std {
// specialize template
template <>
struct hash<smt::SolverEnum>
{
  size_t operator()(const smt::SolverEnum se) const
  {
    return static_cast<size_t>(se);
  }
};

// specialize template
template <>
struct hash<smt::SolverAttribute>
{
  size_t operator()(const smt::SolverAttribute sa) const
  {
    return static_cast<size_t>(sa);
  }
};

}  // namespace std
