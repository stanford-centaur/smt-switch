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
        { BTOR, { TERMITER, ARRAY_MODELS, CONSTARR, UNSAT_CORE } },

        { BTOR_LOGGING,
          { LOGGING,
            TERMITER,
            ARRAY_MODELS,
            CONSTARR,
            FULL_TRANSFER,
            UNSAT_CORE } },

        { CVC4,
          {
              TERMITER,
              THEORY_INT,
              // TODO: put this back after getStoreAllBase() is in API
              // ARRAY_MODELS,
              CONSTARR,
              FULL_TRANSFER,
              UNSAT_CORE,
              THEORY_DATATYPE,
          } },

        { CVC4_LOGGING,
          { LOGGING,
            TERMITER,
            THEORY_INT,
            // TODO: put this back after getStoreAllBase() is in API
            // ARRAY_MODELS,
            CONSTARR,
            FULL_TRANSFER,
            UNSAT_CORE } },

        { MSAT,
          { TERMITER,
            THEORY_INT,
            ARRAY_MODELS,
            CONSTARR,
            FULL_TRANSFER,
            UNSAT_CORE } },

        { MSAT_LOGGING,
          { LOGGING,
            TERMITER,
            THEORY_INT,
            ARRAY_MODELS,
            CONSTARR,
            FULL_TRANSFER,
            UNSAT_CORE } },

        // TODO: Yices2 should support UNSAT_CORE
        //       but something funky happens with testing
        //       has something to do with the context and yices_init
        //       look into this more and re-enable it
        { YICES2, { THEORY_INT } },

        { YICES2_LOGGING,
          { LOGGING, TERMITER, THEORY_INT, FULL_TRANSFER, UNSAT_CORE } },

    });

const unordered_set<SolverEnum> logging_solver_enums(
    { BTOR_LOGGING, CVC4_LOGGING, MSAT_LOGGING, YICES2_LOGGING });
const unordered_map<SolverEnum, SolverEnum> to_logging_solver_enum(
    { { BTOR, BTOR_LOGGING },
      { CVC4, CVC4_LOGGING },
      { MSAT, MSAT_LOGGING },
      { YICES2, YICES2_LOGGING } });

bool is_logging(SolverEnum se)
{
  return logging_solver_enums.find(se) != logging_solver_enums.end();
}

SolverEnum get_logging_solver_enum(SolverEnum se)
{
  if (is_logging(se))
  {
    throw IncorrectUsageException("Expecting non-logging solver enum but got "
                                  + to_string(se));
  }
  else if (to_logging_solver_enum.find(se) == to_logging_solver_enum.end())
  {
    throw NotImplementedException(
        "Don't have a mapping from solver enum to logging version for "
        + to_string(se));
  }

  return to_logging_solver_enum.at(se);
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
    case CVC4: o << "CVC4"; break;
    case MSAT: o << "MSAT"; break;
    case YICES2: o << "YICES2"; break;
    case BTOR_LOGGING: o << "BTOR_LOGGING"; break;
    case CVC4_LOGGING: o << "CVC4_LOGGING"; break;
    case MSAT_LOGGING: o << "MSAT_LOGGING"; break;
    case YICES2_LOGGING: o << "YICES2_LOGGING"; break;
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

}  // namespace smt
