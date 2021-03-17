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
            CONSTARR,
            UNSAT_CORE,
            QUANTIFIERS,
            GET_OP,
            BOOL_BV1_ALIASING } },

        { BZLA,
          { TERMITER,
            CONSTARR,
            UNSAT_CORE,
            QUANTIFIERS,
            GET_OP,
            BOOL_BV1_ALIASING } },

        { CVC4,
          { TERMITER,
            THEORY_INT,
            THEORY_REAL,
            ARRAY_MODELS,
            ARRAY_FUN_BOOLS,
            CONSTARR,
            FULL_TRANSFER,
            UNSAT_CORE,
            THEORY_DATATYPE,
            QUANTIFIERS,
            GET_OP } },

        { GENERIC_SOLVER,
          {
              TERMITER,
              THEORY_INT,
              THEORY_REAL,
              ARRAY_FUN_BOOLS,
              UNSAT_CORE,
              QUANTIFIERS
          } },


        { MSAT,
          { TERMITER,
            THEORY_INT,
            THEORY_REAL,
            ARRAY_MODELS,
            CONSTARR,
            FULL_TRANSFER,
            UNSAT_CORE,
            QUANTIFIERS,
            GET_OP } },

        // TODO: Yices2 should support UNSAT_CORE
        //       but something funky happens with testing
        //       has something to do with the context and yices_init
        //       look into this more and re-enable it
        { YICES2, { LOGGING, THEORY_INT, THEORY_REAL, ARRAY_FUN_BOOLS } },
        { Z3,
          {
              LOGGING,
              THEORY_INT,
              THEORY_REAL,
              ARRAY_FUN_BOOLS,
              CONSTARR,
              QUANTIFIERS
          } },

    });

const unordered_set<SolverEnum> interpolator_solver_enums(
    { MSAT_INTERPOLATOR, CVC4_INTERPOLATOR });

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
    case CVC4: o << "CVC4"; break;
    case MSAT: o << "MSAT"; break;
    case YICES2: o << "YICES2"; break;
    case Z3: o << "Z3"; break;
    case MSAT_INTERPOLATOR: o << "MSAT_INTERPOLATOR"; break;
    case CVC4_INTERPOLATOR: o << "CVC4_INTERPOLATOR"; break;
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
