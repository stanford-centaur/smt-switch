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

#include <algorithm>

using namespace smt;

namespace smt_tests {

// list of regular (non-interpolator) solver enums
const std::vector<SolverEnum> solver_enums({
#if BUILD_BTOR
  BTOR,
#endif

#if BUILD_CVC4
      CVC4,
#endif

#if BUILD_MSAT
      MSAT,
#endif

#if BUILD_YICES2
      YICES2,
#endif
});

SmtSolver create_solver(SolverConfiguration sc)
{
  SolverEnum se = sc.solver_enum;
  bool logging = sc.is_logging_solver;
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

SmtSolver create_interpolating_solver(SolverConfiguration sc) {
  SolverEnum se = sc.solver_enum;
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

std::vector<SolverConfiguration> available_solver_configurations()
{
  std::vector<SolverConfiguration> configs;
  for (SolverEnum e : available_solver_enums())
  {
    SolverConfiguration sct(e, true);
    SolverConfiguration scf(e, false);
    configs.push_back(sct);
    configs.push_back(scf);
  }
  return configs;
}

std::vector<SolverEnum> available_interpolator_enums()
{
  std::vector<SolverEnum> result;
#if BUILD_MSAT
  result.push_back(MSAT_INTERPOLATOR);
#endif
#if BUILD_CVC4
  result.push_back(CVC4_INTERPOLATOR);
#endif

  return result;
}

std::vector<SolverConfiguration> available_interpolator_configurations()
{
  std::vector<SolverConfiguration> result;
  for (SolverEnum e : available_interpolator_enums()) {
    SolverConfiguration sc(e, false);
    result.push_back(sc);
  }
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

std::vector<SolverConfiguration> filter_solver_configurations(
    const std::unordered_set<SolverAttribute> attributes)
{
  // first get the enums
  std::vector<SolverEnum> filtered_enums = filter_solver_enums(attributes);

  // compute result
  std::vector<SolverConfiguration> result;
  for (SolverEnum e : filtered_enums) {
    SolverConfiguration scf(e, false);
    SolverConfiguration sct(e, true);
    result.push_back(scf);
    result.push_back(sct);
  }

  // there are some features that logging solvers support even if the base
  // solver does not
  if (attributes.find(TERMITER) != attributes.end()
      || attributes.find(FULL_TRANSFER) != attributes.end())
  {
    std::unordered_set<SolverAttribute> reduced_attributes = attributes;
    reduced_attributes.erase(TERMITER);
    reduced_attributes.erase(FULL_TRANSFER);
    // get filtered enums for the rest of the attributes
    std::vector<SolverEnum> reduced_filtered_enums =
        filter_solver_enums(reduced_attributes);
    std::unordered_set<SolverEnum> filtered_enums_set(filtered_enums.begin(),
                                                      filtered_enums.end());
    for (auto se : reduced_filtered_enums)
    {
      if (filtered_enums_set.find(se) == filtered_enums_set.end())
      {
        result.push_back(SolverConfiguration(se, true));
      }
    }
  }
  return result;
}

}  // namespace smt_tests
