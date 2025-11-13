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

#include <ostream>
#include <string>
#include <unordered_set>
#include <vector>

#include "exceptions.h"
#include "logging_solver.h"
#include "test-utils.h"

#if BUILD_BTOR
#include "boolector_factory.h"
#endif

#if BUILD_BITWUZLA
#include "bitwuzla_factory.h"
#endif

#if BUILD_CVC5
#include "cvc5_factory.h"
#include "generic_solver.h"
#endif

#if BUILD_MSAT
#include "msat_factory.h"
#endif

#if BUILD_YICES2
#include "yices2_factory.h"
#endif

#if BUILD_Z3
#include "z3_factory.h"
#endif

using namespace smt;

namespace smt_tests {

// list of regular (non-interpolator) solver enums
const std::vector<SolverEnum> solver_enums({
#if BUILD_BTOR
    BTOR,
#endif
#if BUILD_BITWUZLA
    BZLA,
#endif
#if BUILD_CVC5
    CVC5,
#ifndef __APPLE__
    GENERIC_SOLVER,
#endif
#endif
#if BUILD_MSAT
    MSAT,
#endif
#if BUILD_YICES2
    YICES2,
#endif
#if BUILD_Z3
    Z3,
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
    }
#endif
#if BUILD_BITWUZLA
    case BZLA: {
      return BitwuzlaSolverFactory::create(logging);
      break;
    }
#endif
#if BUILD_CVC5
    case CVC5: {
      return Cvc5SolverFactory::create(logging);
      break;
    }
#ifndef __APPLE__
    case GENERIC_SOLVER: {
      std::string path = (STRFY(CVC5_HOME));
      path += "/build/bin/cvc5";
      std::vector<std::string> args = {
        "--lang=smt2", "--incremental", "--dag-thresh=0", "-q"
      };
      SmtSolver generic_solver =
          std::make_shared<GenericSolver>(path, args, 5, 5);
      if (logging)
      {
        return std::make_shared<LoggingSolver>(generic_solver);
      }
      else
      {
        return std::make_shared<GenericSolver>(path, args, 5, 5);
      }
      break;
    }
#endif
#endif
#if BUILD_MSAT
    case MSAT: {
      return MsatSolverFactory::create(logging);
      break;
    }
#endif
#if BUILD_YICES2
    case YICES2: {
      return Yices2SolverFactory::create(logging);
      break;
    }
#endif
#if BUILD_Z3
    case Z3: {
      return Z3SolverFactory::create(logging);
      break;
    }
#endif
    default: {
      throw SmtException("Unhandled solver enum");
    }
  }
}

SmtSolver create_interpolating_solver(SolverConfiguration sc)
{
  SolverEnum se = sc.solver_enum;
  switch (se)
  {
#if BUILD_CVC5
    case CVC5_INTERPOLATOR: {
      return Cvc5SolverFactory::create_interpolating_solver();
      break;
    }
#endif
#if BUILD_MSAT
    case MSAT_INTERPOLATOR: {
      return MsatSolverFactory::create_interpolating_solver();
      break;
    }
#endif
    default: {
      throw SmtException("Unhandled solver enum");
    }
  }
}

std::vector<SolverEnum> available_solver_enums() { return solver_enums; }

std::vector<SolverEnum> available_non_generic_solver_enums()
{
  std::vector<SolverEnum> result;
  for (SolverEnum se : solver_enums)
  {
    if (se != SolverEnum::GENERIC_SOLVER)
    {
      result.push_back(se);
    }
  }
  return result;
}

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

std::vector<SolverConfiguration> available_non_generic_solver_configurations()
{
  std::vector<SolverConfiguration> original = available_solver_configurations();
  std::vector<SolverConfiguration> result;
  for (SolverConfiguration sc : original)
  {
    if (sc.solver_enum != SolverEnum::GENERIC_SOLVER)
    {
      result.push_back(sc);
    }
  }
  return result;
}

std::vector<SolverEnum> available_interpolator_enums()
{
  std::vector<SolverEnum> result;
#if BUILD_CVC5
  result.push_back(CVC5_INTERPOLATOR);
#endif
#if BUILD_MSAT
  result.push_back(MSAT_INTERPOLATOR);
#endif
  return result;
}

std::vector<SolverConfiguration> available_interpolator_configurations()
{
  std::vector<SolverConfiguration> result;
  for (SolverEnum e : available_interpolator_enums())
  {
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
  for (SolverEnum e : filtered_enums)
  {
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

std::vector<SolverConfiguration> filter_non_generic_solver_configurations(
    const std::unordered_set<SolverAttribute> attributes)
{
  std::vector<SolverConfiguration> original_result =
      filter_solver_configurations(attributes);
  std::vector<SolverConfiguration> result;
  for (SolverConfiguration sc : original_result)
  {
    if (sc.solver_enum != SolverEnum::GENERIC_SOLVER)
    {
      result.push_back(sc);
    }
  }
  return result;
}

std::ostream & operator<<(std::ostream & o, SolverConfiguration sc)
{
  o << sc.solver_enum << "(logging=" << sc.is_logging_solver << ")";
  return o;
}

}  // namespace smt_tests
