/*!
 * \file solver_enums.cpp
 * \brief Convenience functions for SolverEnums
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/solver_enums.h"

#include <optional>
#include <sstream>
#include <string>
#include <unordered_set>

#include "smt-switch/exceptions.h"

namespace smt {

SolverKind solver_kind(InterpolatorKind itp_kind)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (itp_kind)
  {
    case InterpolatorKind::BZLA: return SolverKind::BZLA;
    case InterpolatorKind::CVC5: return SolverKind::CVC5;
    case InterpolatorKind::MSAT: return SolverKind::MSAT;
    case InterpolatorKind::YICES2: return SolverKind::YICES2;
  }
  throw NotImplementedException("Unknown InterpolatorKind: "
                                + std::to_string(static_cast<int>(itp_kind)));
}

bool solver_has_attribute(SolverKind solver_kind, SolverAttribute sa)
{
  std::unordered_set<SolverAttribute> solver_attrs =
      get_solver_attributes(solver_kind);
  return solver_attrs.find(sa) != solver_attrs.end();
}

std::unordered_set<SolverAttribute> get_solver_attributes(
    SolverKind solver_kind)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (solver_kind)
  {
    case SolverKind::BTOR:
      return { TERMITER,   ARRAY_MODELS, THEORY_BV,         CONSTARR,
               UNSAT_CORE, QUANTIFIERS,  BOOL_BV1_ALIASING, TIMELIMIT };
    // Bitwuzla reasons over terms of uninterpreted sorts in functions,
    // arrays and ite, but answers unknown to an equality between two of
    // them that its preprocessing cannot remove.
    case SolverKind::BZLA:
      return { TERMITER,      ARRAY_MODELS,       CONSTARR,    FULL_TRANSFER,
               UNSAT_CORE,    THEORY_BV,          QUANTIFIERS, TIMELIMIT,
               UNINTERP_SORT, PARAM_UNINTERP_SORT };
    case SolverKind::CVC5:
      return { TERMITER,      THEORY_INT,          THEORY_STR,      THEORY_BV,
               THEORY_REAL,   ARRAY_MODELS,        ARRAY_FUN_BOOLS, CONSTARR,
               FULL_TRANSFER, UNSAT_CORE,          THEORY_DATATYPE, QUANTIFIERS,
               UNINTERP_SORT, PARAM_UNINTERP_SORT, TIMELIMIT };
    case SolverKind::GENERIC:
      return { TERMITER,      ARRAY_MODELS,       THEORY_INT,
               THEORY_BV,     THEORY_REAL,        ARRAY_FUN_BOOLS,
               UNSAT_CORE,    THEORY_DATATYPE,    QUANTIFIERS,
               UNINTERP_SORT, PARAM_UNINTERP_SORT };
    case SolverKind::MSAT:
      return {
        TERMITER, THEORY_INT,    THEORY_BV,  THEORY_REAL,   ARRAY_MODELS,
        CONSTARR, FULL_TRANSFER, UNSAT_CORE, UNINTERP_SORT, PARAM_UNINTERP_SORT,
        TIMELIMIT
      };
    case SolverKind::YICES2:
      return {
        LOGGING,      CONSTARR,      FULL_TRANSFER,       TERMITER,
        THEORY_INT,   THEORY_BV,     THEORY_REAL,         ARRAY_FUN_BOOLS,
        ARRAY_MODELS, UNINTERP_SORT, PARAM_UNINTERP_SORT, TIMELIMIT,
        UNSAT_CORE
      };
    case SolverKind::Z3:
      return { TERMITER,        LOGGING,
               THEORY_INT,      THEORY_BV,
               THEORY_REAL,     ARRAY_FUN_BOOLS,
               ARRAY_MODELS,    CONSTARR,
               FULL_TRANSFER,   UNSAT_CORE,
               THEORY_DATATYPE, QUANTIFIERS,
               UNINTERP_SORT,   PARAM_UNINTERP_SORT,
               TIMELIMIT };
  }
  throw NotImplementedException(
      "Unknown SolverKind: " + std::to_string(static_cast<int>(solver_kind)));
}

std::ostream & operator<<(std::ostream & o, SolverKind solver_kind)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (solver_kind)
  {
    case SolverKind::BTOR: return o << "BTOR";
    case SolverKind::BZLA: return o << "BZLA";
    case SolverKind::CVC5: return o << "CVC5";
    case SolverKind::GENERIC: return o << "GENERIC";
    case SolverKind::MSAT: return o << "MSAT";
    case SolverKind::YICES2: return o << "YICES2";
    case SolverKind::Z3: return o << "Z3";
  }
  throw NotImplementedException(
      "Unknown SolverKind: " + std::to_string(static_cast<int>(solver_kind)));
}

std::string to_string(SolverKind solver_kind)
{
  std::ostringstream ostr;
  ostr << solver_kind;
  return ostr.str();
}

std::ostream & operator<<(std::ostream & o, InterpolatorKind itp_kind)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (itp_kind)
  {
    case InterpolatorKind::BZLA: return o << "BZLA";
    case InterpolatorKind::CVC5: return o << "CVC5";
    case InterpolatorKind::MSAT: return o << "MSAT";
    case InterpolatorKind::YICES2: return o << "YICES2";
  }
  throw NotImplementedException("Unknown InterpolatorKind: "
                                + std::to_string(static_cast<int>(itp_kind)));
}

std::string to_string(InterpolatorKind itp_kind)
{
  std::ostringstream ostr;
  ostr << itp_kind;
  return ostr.str();
}

std::ostream & operator<<(std::ostream & o, SolverAttribute a)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (a)
  {
    case LOGGING: return o << "LOGGING";
    case TERMITER: return o << "TERMITER";
    case THEORY_BV: return o << "THEORY_BV";
    case THEORY_INT: return o << "THEORY_INT";
    case THEORY_REAL: return o << "THEORY_REAL";
    case THEORY_STR: return o << "THEORY_STR";
    case ARRAY_MODELS: return o << "ARRAY_MODELS";
    case CONSTARR: return o << "CONSTARR";
    case FULL_TRANSFER: return o << "FULL_TRANSFER";
    case ARRAY_FUN_BOOLS: return o << "ARRAY_FUN_BOOLS";
    case UNSAT_CORE: return o << "UNSAT_CORE";
    case THEORY_DATATYPE: return o << "THEORY_DATATYPE";
    case QUANTIFIERS: return o << "QUANTIFIERS";
    case UNINTERP_SORT: return o << "UNINTERP_SORT";
    case PARAM_UNINTERP_SORT: return o << "PARAM_UNINTERP_SORT";
    case BOOL_BV1_ALIASING: return o << "BOOL_BV1_ALIASING";
    case TIMELIMIT: return o << "TIMELIMIT";
  }
  throw NotImplementedException("Unknown SolverAttribute: "
                                + std::to_string(a));
}

std::string to_string(SolverAttribute a)
{
  std::ostringstream ostr;
  ostr << a;
  return ostr.str();
}

SolverKind detail::solver_kind(SolverEnum se)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (se)
  {
    case BTOR: return SolverKind::BTOR;
    case BZLA:
    case BZLA_INTERPOLATOR: return SolverKind::BZLA;
    case CVC5:
    case CVC5_INTERPOLATOR: return SolverKind::CVC5;
    case GENERIC_SOLVER: return SolverKind::GENERIC;
    case MSAT:
    case MSAT_INTERPOLATOR: return SolverKind::MSAT;
    case YICES2:
    case YICES2_INTERPOLATOR: return SolverKind::YICES2;
    case Z3: return SolverKind::Z3;
  }
  throw NotImplementedException("Unknown SolverEnum: " + std::to_string(se));
}

/** The interpolator se identifies, or none for a regular solver */
static std::optional<InterpolatorKind> interpolator_kind(SolverEnum se)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (se)
  {
    case BTOR:
    case BZLA:
    case CVC5:
    case GENERIC_SOLVER:
    case MSAT:
    case YICES2:
    case Z3: return std::nullopt;
    case BZLA_INTERPOLATOR: return InterpolatorKind::BZLA;
    case CVC5_INTERPOLATOR: return InterpolatorKind::CVC5;
    case MSAT_INTERPOLATOR: return InterpolatorKind::MSAT;
    case YICES2_INTERPOLATOR: return InterpolatorKind::YICES2;
  }
  throw NotImplementedException("Unknown SolverEnum: " + std::to_string(se));
}

SolverEnum detail::solver_enum(SolverKind solver_kind)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (solver_kind)
  {
    case SolverKind::BTOR: return BTOR;
    case SolverKind::BZLA: return BZLA;
    case SolverKind::CVC5: return CVC5;
    case SolverKind::GENERIC: return GENERIC_SOLVER;
    case SolverKind::MSAT: return MSAT;
    case SolverKind::YICES2: return YICES2;
    case SolverKind::Z3: return Z3;
  }
  throw NotImplementedException(
      "Unknown SolverKind: " + std::to_string(static_cast<int>(solver_kind)));
}

SolverEnum detail::solver_enum(InterpolatorKind itp_kind)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (itp_kind)
  {
    case InterpolatorKind::BZLA: return BZLA_INTERPOLATOR;
    case InterpolatorKind::CVC5: return CVC5_INTERPOLATOR;
    case InterpolatorKind::MSAT: return MSAT_INTERPOLATOR;
    case InterpolatorKind::YICES2: return YICES2_INTERPOLATOR;
  }
  throw NotImplementedException("Unknown InterpolatorKind: "
                                + std::to_string(static_cast<int>(itp_kind)));
}

bool is_interpolator_solver_enum(SolverEnum se)
{
  return interpolator_kind(se).has_value();
}

bool solver_has_attribute(SolverEnum se, SolverAttribute sa)
{
  return solver_has_attribute(detail::solver_kind(se), sa);
}

std::unordered_set<SolverAttribute> get_solver_attributes(SolverEnum se)
{
  return get_solver_attributes(detail::solver_kind(se));
}

std::ostream & operator<<(std::ostream & o, SolverEnum e)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (e)
  {
    case BTOR: return o << "BTOR";
    case BZLA: return o << "BZLA";
    case CVC5: return o << "CVC5";
    case GENERIC_SOLVER: return o << "GENERIC_SOLVER";
    case MSAT: return o << "MSAT";
    case YICES2: return o << "YICES2";
    case Z3: return o << "Z3";
    case BZLA_INTERPOLATOR: return o << "BZLA_INTERPOLATOR";
    case CVC5_INTERPOLATOR: return o << "CVC5_INTERPOLATOR";
    case MSAT_INTERPOLATOR: return o << "MSAT_INTERPOLATOR";
    case YICES2_INTERPOLATOR: return o << "YICES2_INTERPOLATOR";
  }
  throw NotImplementedException("Unknown SolverEnum: " + std::to_string(e));
}

std::string to_string(SolverEnum e)
{
  std::ostringstream ostr;
  ostr << e;
  return ostr.str();
}

SolverKind to_solver_kind(SolverEnum se)
{
  if (interpolator_kind(se))
  {
    throw IncorrectUsageException("Not a regular solver: "
                                  + std::to_string(se));
  }
  return detail::solver_kind(se);
}

InterpolatorKind to_interpolator_kind(SolverEnum se)
{
  std::optional<InterpolatorKind> itp_kind = interpolator_kind(se);
  if (!itp_kind)
  {
    throw IncorrectUsageException("Not an interpolator: " + std::to_string(se));
  }
  return *itp_kind;
}

SolverEnum to_solver_enum(SolverKind solver_kind)
{
  return detail::solver_enum(solver_kind);
}

SolverEnum to_solver_enum(InterpolatorKind itp_kind)
{
  return detail::solver_enum(itp_kind);
}

}  // namespace smt
