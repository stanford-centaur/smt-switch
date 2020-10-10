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

// list of regular (non-interpolator) solver enums
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

SmtSolver create_solver(SolverConfiguration sc)
{
  SolverEnum se = sc.get_solver_enum();
  bool logging = sc.get_is_logging_solver();
  switch (se)
  {
#if BUILD_BTOR
    case BTOR: {
      return BoolectorSolverFactory::create(logging);
      break;
      ;
    }
#endif
#if BUILD_CVC4
    case CVC4: {
      return CVC4SolverFactory::create(logging);
      break;
      ;
    }
#endif
#if BUILD_MSAT
    case MSAT: {
      return MsatSolverFactory::create(logging);
      break;
      ;
    }
#endif
#if BUILD_YICES2
    case YICES2: {
      return Yices2SolverFactory::create(logging);
      break;
      ;
    }
#endif
    default: {
      throw SmtException("Unhandled solver enum");
    }
  }
}

SmtSolver create_interpolating_solver(SolverEnum se)
{
  switch (se)
  {
#if BUILD_MSAT
    case MSAT_INTERPOLATOR:
    {
      return MsatSolverFactory::create_interpolating_solver();
      break;
      ;
    }
#endif
#if BUILD_CVC4
    case CVC4_INTERPOLATOR:
    {
      return CVC4SolverFactory::create_interpolating_solver();
      break;
      ;
    }
#endif
    default: { throw SmtException("Unhandled solver enum");
    }
  }
}

std::vector<SolverEnum> available_solver_enums() { return solver_enums; }

SolverConfiguration::SolverConfiguration(SolverEnum e, bool logging)
    : solver_enum(e), is_logging_solver(logging)
{
}

std::vector<SolverConfiguration> available_solver_configurations()
{
  std::vector<SolverConfiguration> configs;
  std::vector<SolverEnum> enums = available_no_logging_solver_enums();
  for (SolverEnum e : enums)
  {
    configs.push_back(SolverConfiguration(e, true));
    configs.push_back(SolverConfiguration(e, false));
  }
  return configs;
}

// collect all the available non-logging solvers
std::vector<SolverEnum> available_no_logging_solver_enums()
{
  std::vector<SolverEnum> enums;
  for (auto se : solver_enums)
  {
    const std::unordered_set<SolverAttribute> & se_attrs =
        get_solver_attributes(se);

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
    const std::unordered_set<SolverAttribute> & se_attrs =
        get_solver_attributes(se);

    if (se_attrs.find(LOGGING) != se_attrs.end())
    {
      enums.push_back(se);
    }
  }
  return enums;
}

std::vector<SolverEnum> available_interpolator_enums() { 
  std::vector<SolverEnum> result;
#if BUILD_MSAT
  result.push_back(MSAT_INTERPOLATOR);
#endif  
#if BUILD_CVC4
  result.push_back(CVC4_INTERPOLATOR);
#endif  

  return result;
}

std::vector<SolverEnum> filter_solver_enums(
    const std::unordered_set<SolverAttribute> attributes)
{
  std::vector<SolverEnum> filtered_enums;
  for (auto se : solver_enums)
  {
    const std::unordered_set<SolverAttribute> & se_attrs =
        get_solver_attributes(se);

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


}  // namespace smt_tests
