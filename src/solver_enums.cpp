/*********************                                                        */
/*! \file solver_enums.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Convenience functions for SolverEnums
**
**
**/

#include "solver_enums.h"

#include <sstream>
#include <unordered_map>
#include <unordered_set>

#include "exceptions.h"

namespace smt {

const std::unordered_map<SolverEnum, std::unordered_set<SolverAttribute>>
    solver_attributes({
        { BTOR,
          { TERMITER,
            ARRAY_MODELS,
            THEORY_BV,
            CONSTARR,
            UNSAT_CORE,
            QUANTIFIERS,
            BOOL_BV1_ALIASING,
            TIMELIMIT } },
        // Bitwuzla declares uninterpreted sorts and constants of them, but
        // cannot reason over them: an equality warns "Equalities over
        // uninterpreted sorts not yet supported" and answers unknown, and a
        // distinct of three or more throws out of check_sat. So it claims
        // neither UNINTERP_SORT nor PARAM_UNINTERP_SORT.
        { BZLA,
          { TERMITER,
            CONSTARR,
            UNSAT_CORE,
            THEORY_BV,
            QUANTIFIERS,
            TIMELIMIT } },
        { CVC5,
          { TERMITER,
            THEORY_INT,
            THEORY_STR,
            THEORY_BV,
            THEORY_REAL,
            ARRAY_MODELS,
            ARRAY_FUN_BOOLS,
            CONSTARR,
            FULL_TRANSFER,
            UNSAT_CORE,
            THEORY_DATATYPE,
            QUANTIFIERS,
            UNINTERP_SORT,
            PARAM_UNINTERP_SORT,
            TIMELIMIT } },
        { GENERIC_SOLVER,
          { TERMITER,
            THEORY_INT,
            THEORY_BV,
            THEORY_REAL,
            ARRAY_FUN_BOOLS,
            UNSAT_CORE,
            THEORY_DATATYPE,
            QUANTIFIERS,
            UNINTERP_SORT,
            PARAM_UNINTERP_SORT } },
        { MSAT,
          { TERMITER,
            THEORY_INT,
            THEORY_BV,
            THEORY_REAL,
            ARRAY_MODELS,
            CONSTARR,
            FULL_TRANSFER,
            UNSAT_CORE,
            QUANTIFIERS,
            UNINTERP_SORT } },
        // TODO: Yices2 should support UNSAT_CORE
        //       but something funky happens with testing
        //       has something to do with the context and yices_init
        //       look into this more and re-enable it
        { YICES2,
          { LOGGING,
            THEORY_INT,
            THEORY_BV,
            THEORY_REAL,
            ARRAY_FUN_BOOLS,
            UNINTERP_SORT,
            TIMELIMIT } },
        { Z3,
          { TERMITER,
            LOGGING,
            THEORY_INT,
            THEORY_BV,
            THEORY_REAL,
            ARRAY_FUN_BOOLS,
            ARRAY_MODELS,
            CONSTARR,
            UNSAT_CORE,
            THEORY_DATATYPE,
            QUANTIFIERS,
            UNINTERP_SORT,
            TIMELIMIT } },
    });

const std::unordered_set<SolverEnum> interpolator_solver_enums({
    BZLA_INTERPOLATOR,
    CVC5_INTERPOLATOR,
    MSAT_INTERPOLATOR,
});

bool is_interpolator_solver_enum(SolverEnum se)
{
  return interpolator_solver_enums.find(se) != interpolator_solver_enums.end();
}

bool solver_has_attribute(SolverEnum se, SolverAttribute sa)
{
  std::unordered_set<SolverAttribute> solver_attrs = get_solver_attributes(se);
  return solver_attrs.find(sa) != solver_attrs.end();
}

std::unordered_set<SolverAttribute> get_solver_attributes(SolverEnum se)
{
  if (solver_attributes.find(se) == solver_attributes.end())
  {
    throw NotImplementedException("Unhandled solver enum: " + to_string(se));
  }

  return solver_attributes.at(se);
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
  }
  throw NotImplementedException("Unknown SolverEnum: " + std::to_string(e));
}

std::string to_string(SolverEnum e)
{
  std::ostringstream ostr;
  ostr << e;
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

}  // namespace smt
