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

#include <iostream>
#include <sstream>
#include <unordered_map>

#include "exceptions.h"
#include "solver_enums.h"

using namespace std;

namespace smt {

const unordered_map<SolverEnum, unordered_set<SolverAttribute>>
    solver_attributes({
        { BTOR,
          { TERMITER,
            ARRAY_MODELS,
            THEORY_BV,
            CONSTARR,
            UNSAT_CORE,
            QUANTIFIERS,
            BOOL_BV1_ALIASING } },

        { BZLA,
          { TERMITER,
            CONSTARR,
            UNSAT_CORE,
            THEORY_BV,
            // TEMP only temporarily disabled until bitwuzla
            //      quantifier refactoring is done
            //      see
            //      https://github.com/bitwuzla/bitwuzla/commit/605f31557ec6c635e3c617d2b0ab257309e994c4
            // QUANTIFIERS,
            BOOL_BV1_ALIASING,
            TIMELIMIT } },

        { CVC5,
          { TERMITER,
            THEORY_INT,
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
            PARAM_UNINTERP_SORT } },

        { GENERIC_SOLVER,
          { TERMITER,
            THEORY_INT,
            THEORY_BV,
            THEORY_REAL,
            ARRAY_FUN_BOOLS,
            UNSAT_CORE,
            THEORY_DATATYPE,
            QUANTIFIERS } },

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
            CONSTARR,
            UNSAT_CORE,
            QUANTIFIERS,
            UNINTERP_SORT,
            TIMELIMIT } },

    });

const unordered_set<SolverEnum> interpolator_solver_enums(
    { MSAT_INTERPOLATOR, CVC5_INTERPOLATOR });

bool is_interpolator_solver_enum(SolverEnum se)
{
  return interpolator_solver_enums.find(se) != interpolator_solver_enums.end();
}

bool solver_has_attribute(SolverEnum se, SolverAttribute sa)
{
  unordered_set<SolverAttribute> solver_attrs = get_solver_attributes(se);
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
  switch (e)
  {
    case BTOR: o << "BTOR"; break;
    case BZLA: o << "BZLA"; break;
    case CVC5: o << "CVC5"; break;
    case MSAT: o << "MSAT"; break;
    case YICES2: o << "YICES2"; break;
    case Z3: o << "Z3"; break;
    case MSAT_INTERPOLATOR: o << "MSAT_INTERPOLATOR"; break;
    case CVC5_INTERPOLATOR: o << "CVC5_INTERPOLATOR"; break;
    case GENERIC_SOLVER: o << "GENERIC_SOLVER"; break;
    default:
      // should print the integer representation
      throw NotImplementedException("Unknown SolverEnum: " + std::to_string(e));
      break;
  }

  return o;
}

std::string to_string(SolverEnum e)
{
  ostringstream ostr;
  ostr << e;
  return ostr.str();
}

std::ostream & operator<<(std::ostream & o, SolverAttribute a)
{
  switch (a)
  {
    case TERMITER: o << "TERMITER"; break;
    case THEORY_INT: o << "THEORY_INT"; break;
    case THEORY_REAL: o << "THEORY_REAL"; break;
    case ARRAY_MODELS: o << "ARRAY_MODELS"; break;
    case CONSTARR: o << "CONSTARR"; break;
    case FULL_TRANSFER: o << "FULL_TRANSFER"; break;
    case ARRAY_FUN_BOOLS: o << "ARRAY_FUN_BOOLS"; break;
    case UNSAT_CORE: o << "UNSAT_CORE"; break;
    case THEORY_DATATYPE: o << "THEORY_DATATYPE"; break;
    case QUANTIFIERS: o << "QUANTIFIERS"; break;
    case BOOL_BV1_ALIASING: o << "BOOL_BV1_ALIASING"; break;
    default:
      // should print the integer representation
      throw NotImplementedException("Unknown SolverAttribute: "
                                    + std::to_string(a));
      break;
  }

  return o;
}

std::string to_string(SolverAttribute a)
{
  ostringstream ostr;
  ostr << a;
  return ostr.str();
}

}  // namespace smt
