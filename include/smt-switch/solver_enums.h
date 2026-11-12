/*!
 * \file solver_enums.h
 * \brief Enums for identifying SmtSolver objects
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_SOLVER_ENUMS_H
#define SMT_SWITCH_SOLVER_ENUMS_H

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#include <ostream>
#include <string>
#include <unordered_set>

namespace smt {

/** The backend of a regular solver */
enum class SolverKind
{
  BTOR,
  BZLA,
  CVC5,
  GENERIC,
  MSAT,
  YICES2,
  Z3
};

/** The backend of an interpolator */
enum class InterpolatorKind
{
  BZLA,
  CVC5,
  MSAT,
  YICES2
};

/** A regular solver's or an interpolator's backend; superseded by
 *  SolverKind and InterpolatorKind, and taken or returned only by
 *  deprecated functions
 */
enum SolverEnum
{
  BTOR = 0,        // boolector
  BZLA,            // bitwuzla
  CVC5,            // cvc5
  GENERIC_SOLVER,  // generic solver (binary)
  MSAT,            // mathsat
  YICES2,          // yices2
  Z3,              // z3

  // interpolating solvers -- note these cannot be logging solvers
  // because the solver takes the initiative in creating the interpolant
  // so there's no way to keep a DAG at the smt-switch level
  BZLA_INTERPOLATOR,
  CVC5_INTERPOLATOR,
  MSAT_INTERPOLATOR,
  YICES2_INTERPOLATOR,

  // NOTE: when adding a new enum, also add it to the python interface, in
  // python/smt_switch/cppenums.pxd and python/smt_switch/solverenums.pyx
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
  // supports STR theory
  THEORY_STR,
  // supports array models
  ARRAY_MODELS,
  // supports constant arrays
  CONSTARR,
  // terms can be traversed with iteration, and a term's Op and children
  // can be used to rebuild an equivalent term in another solver
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
  // supports setting a time limit, in seconds (fractions allowed)
  TIMELIMIT

  // NOTE: when adding a new enum, also add it to the python interface, in
  // python/smt_switch/cppenums.pxd and python/smt_switch/solverattr.pyx
};

/** @return the kind of the regular solver that builds the terms of an
 *          interpolator of kind itp_kind, whose attributes it shares
 */
SolverKind solver_kind(InterpolatorKind itp_kind);

bool solver_has_attribute(SolverKind solver_kind, SolverAttribute sa);

std::unordered_set<SolverAttribute> get_solver_attributes(
    SolverKind solver_kind);

std::ostream & operator<<(std::ostream & o, SolverKind solver_kind);

std::string to_string(SolverKind solver_kind);

std::ostream & operator<<(std::ostream & o, InterpolatorKind itp_kind);

std::string to_string(InterpolatorKind itp_kind);

std::ostream & operator<<(std::ostream & o, SolverAttribute sa);

std::string to_string(SolverAttribute a);

/** Returns true iff the SolverEnum corresponds to an Interpolator
 *  @param se the solver enum to check
 *  @return true iff the se is a *_INTERPOLATOR enum
 */
[[deprecated("use SolverKind or InterpolatorKind")]] bool
is_interpolator_solver_enum(SolverEnum se);

[[deprecated("use the SolverKind overload")]] bool solver_has_attribute(
    SolverEnum se, SolverAttribute sa);

[[deprecated(
    "use the SolverKind overload")]] std::unordered_set<SolverAttribute>
get_solver_attributes(SolverEnum se);

std::ostream & operator<<(std::ostream & o, SolverEnum e);

std::string to_string(SolverEnum e);

/** @throws IncorrectUsageException for an interpolator's enumerator */
[[deprecated("use SolverKind")]] SolverKind to_solver_kind(SolverEnum se);

/** @throws IncorrectUsageException for a regular solver's enumerator */
[[deprecated("use InterpolatorKind")]] InterpolatorKind to_interpolator_kind(
    SolverEnum se);

[[deprecated("use SolverKind")]] SolverEnum to_solver_enum(
    SolverKind solver_kind);

[[deprecated("use InterpolatorKind")]] SolverEnum to_solver_enum(
    InterpolatorKind itp_kind);

namespace detail {

// The conversions the deprecated functions in several files are built on,
// as GCC warns where one deprecated function calls another; they go when
// SolverEnum does

/** The backend of se; an interpolator's is the regular solver that builds
 *  its terms
 */
SolverKind solver_kind(SolverEnum se);

SolverEnum solver_enum(SolverKind solver_kind);

SolverEnum solver_enum(InterpolatorKind itp_kind);

}  // namespace detail

}  // namespace smt

#endif  // SMT_SWITCH_SOLVER_ENUMS_H
