/*********************                                                        */
/*! \file available_solvers.cpp
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

#include "available_solvers.h"
#include "exceptions.h"

#if BUILD_BTOR
#include "boolector_factory.h"
#endif

#if BUILD_CVC4
#include "cvc4_factory.h"
#endif

#if BUILD_MSAT
#include "msat_factory.h"
#endif

#if BUILD_YICES2
#include "yices2_factory.h"
#endif

using namespace smt;

namespace smt_tests {

const std::vector<SolverEnum> solver_enums({
#if BUILD_BTOR
  BTOR, BTOR_LOGGING,
#endif

#if BUILD_CVC4
      CVC4, CVC4_LOGGING,
#endif

#if BUILD_MSAT
      MSAT, MSAT_LOGGING,
#endif

#if BUILD_YICES2
      YICES2, YICES2_LOGGING,
#endif
});

const std::unordered_map<SolverEnum, std::unordered_set<SolverAttribute>>
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

SmtSolver create_solver(SolverEnum se)
{
  switch (se)
  {
#if BUILD_BTOR
    case BTOR:
    {
      return BoolectorSolverFactory::create(false);
      break;
      ;
    }
    case BTOR_LOGGING:
    {
      return BoolectorSolverFactory::create(true);
      break;
      ;
    }
#endif
#if BUILD_CVC4
    case CVC4:
    {
      return CVC4SolverFactory::create(false);
      break;
      ;
    }
    case CVC4_LOGGING:
    {
      return CVC4SolverFactory::create(true);
      break;
      ;
    }
#endif
#if BUILD_MSAT
    case MSAT:
    {
      return MsatSolverFactory::create(false);
      break;
      ;
    }
    case MSAT_LOGGING:
    {
      return MsatSolverFactory::create(true);
      break;
      ;
    }
#endif
#if BUILD_YICES2
    case YICES2:
    {
      return Yices2SolverFactory::create(false);
      break;
      ;
    }
    case YICES2_LOGGING:
    {
      return Yices2SolverFactory::create(true);
      break;
      ;
    }
#endif
    default: { throw SmtException("Unhandled solver enum");
    }
  }
}

SmtSolver create_interpolating_solver(SolverEnum se)
{
  switch (se)
  {
#if BUILD_MSAT
    case MSAT:
    {
      return MsatSolverFactory::create_interpolating_solver();
      break;
      ;
    }
#endif
    default: { throw SmtException("Unhandled solver enum");
    }
  }
}

const std::vector<SolverEnum> itp_enums({
#if BUILD_MSAT
  MSAT
#endif
});

std::vector<SolverEnum> available_solver_enums() { return solver_enums; }

// collect all the available non-logging solvers
std::vector<SolverEnum> available_no_logging_solver_enums()
{
  std::vector<SolverEnum> enums;
  for (auto se : solver_enums)
  {
    if (solver_attributes.find(se) == solver_attributes.end())
    {
      throw SmtException("Unhandled solver enum in solver_attributes");
    }

    const std::unordered_set<SolverAttribute> & se_attrs =
        solver_attributes.at(se);
    if (se_attrs.find(LOGGING) == se_attrs.end())
    {
      enums.push_back(se);
    }
  }
  return enums;
}

// collect all the available logging solvers
std::vector<SolverEnum> available_logging_solver_enums()
{
  std::vector<SolverEnum> enums;
  for (auto se : solver_enums)
  {
    if (solver_attributes.find(se) == solver_attributes.end())
    {
      throw SmtException("Unhandled solver enum in solver_attributes");
    }

    const std::unordered_set<SolverAttribute> & se_attrs =
        solver_attributes.at(se);
    if (se_attrs.find(LOGGING) != se_attrs.end())
    {
      enums.push_back(se);
    }
  }
  return enums;
}

std::vector<SolverEnum> available_interpolator_enums() { return itp_enums; };

std::vector<SolverEnum> filter_solver_enums(
    const std::unordered_set<SolverAttribute> attributes)
{
  std::vector<SolverEnum> filtered_enums;
  for (auto se : solver_enums)
  {
    if (solver_attributes.find(se) == solver_attributes.end())
    {
      throw SmtException("Unhandled solver enum in solver_attributes");
    }

    const std::unordered_set<SolverAttribute> & se_attrs =
        solver_attributes.at(se);

    bool all_attrs = true;
    for (auto a : attributes)
    {
      if (se_attrs.find(a) == se_attrs.end())
      {
        all_attrs = false;
        break;
      }
    }

    if (all_attrs)
    {
      filtered_enums.push_back(se);
    }
  }

  return filtered_enums;
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

}  // namespace smt_tests
