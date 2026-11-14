/*!
 * \file available_solvers.cpp
 * \brief Convenience functions for testing
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * They collect the available solvers and filter them by solver attribute.
 */
#include "available_solvers.h"

#include <algorithm>
#include <chrono>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/generic_solver.h"
#include "smt-switch/logging_solver.h"
#include "smt-switch/solver_factory.h"
#include "test_paths.h"

using namespace smt;

namespace smt_tests {

SolverConfiguration::SolverConfiguration(smt::SolverEnum se, bool ils)
    : solver_enum(se), is_logging_solver(ils)
{
}

SmtSolver create_solver(SolverConfiguration sc)
{
  if (sc.solver_enum != GENERIC_SOLVER)
  {
    return smt::create_solver(sc.solver_enum, sc.is_logging_solver);
  }
  std::string path(solver_binary(CVC5));
  std::vector<std::string> args = {
    "--lang=smt2", "--incremental", "--dag-thresh=0", "-q"
  };
  // The queries the tests put to this solver are small enough that
  // cvc5 answers each one, start-up included, in single-digit
  // milliseconds. The library default is a deadlock backstop sized
  // for genuine solving, which would leave a wedged test sitting in
  // CI for an hour; this is still hundreds of times the slack needed.
  const std::chrono::seconds response_timeout(2);
  SmtSolver generic_solver =
      std::make_shared<GenericSolver>(path, args, response_timeout, 5);
  if (sc.is_logging_solver)
  {
    return std::make_shared<LoggingSolver>(generic_solver);
  }
  return generic_solver;
}

std::vector<SolverEnum> available_solver_enums_with_generic()
{
  std::vector<SolverEnum> enums = smt::available_solver_enums();
  // the generic solver drives the cvc5 executable
  if (!solver_binary(CVC5).empty())
  {
    enums.push_back(GENERIC_SOLVER);
  }
  return enums;
}

std::string_view solver_binary(SolverEnum se)
{
  switch (se)
  {
    case BTOR: return smt_tests::boolector_binary;
    case BZLA: return smt_tests::bitwuzla_binary;
    case CVC5: return smt_tests::cvc5_binary;
    case MSAT: return smt_tests::mathsat_binary;
    case YICES2: return smt_tests::yices2_binary;
    case Z3: return smt_tests::z3_binary;
    default: return "";
  }
}

std::vector<SolverConfiguration> available_solver_configurations_with_generic()
{
  std::vector<SolverConfiguration> configs;
  for (SolverEnum e : available_solver_enums_with_generic())
  {
    SolverConfiguration sct(e, true);
    SolverConfiguration scf(e, false);
    configs.push_back(sct);
    configs.push_back(scf);
  }
  return configs;
}

std::vector<SolverConfiguration> available_solver_configurations()
{
  std::vector<SolverConfiguration> original =
      available_solver_configurations_with_generic();
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

std::vector<SolverConfiguration> available_interpolator_configurations()
{
  std::vector<SolverConfiguration> result;
  for (SolverEnum e : smt::available_interpolator_enums())
  {
    SolverConfiguration sc(e, false);
    result.push_back(sc);
  }
  return result;
}

namespace {

/** Whether se has every one of the attributes */
bool has_all_attributes(SolverEnum se,
                        const std::unordered_set<SolverAttribute> & attributes)
{
  const std::unordered_set<SolverAttribute> se_attrs =
      get_solver_attributes(se);
  return std::all_of(
      attributes.begin(), attributes.end(), [&se_attrs](SolverAttribute a) {
        return se_attrs.find(a) != se_attrs.end();
      });
}

}  // namespace

SolverEnum interpolator_base_solver(SolverEnum se)
{
  switch (se)
  {
    case BZLA_INTERPOLATOR: return BZLA;
    case CVC5_INTERPOLATOR: return CVC5;
    case MSAT_INTERPOLATOR: return MSAT;
    case YICES2_INTERPOLATOR: return YICES2;
    default: {
      throw Exception("Unhandled interpolator solver enum");
    }
  }
}

std::vector<SolverConfiguration> filter_interpolator_configurations(
    const std::unordered_set<SolverAttribute> attributes)
{
  std::vector<SolverConfiguration> result;
  for (SolverConfiguration sc : available_interpolator_configurations())
  {
    if (has_all_attributes(sc.solver_enum, attributes))
    {
      result.push_back(sc);
    }
  }
  return result;
}

std::vector<SolverEnum> filter_solver_enums_with_generic(
    const std::unordered_set<SolverAttribute> attributes)
{
  std::vector<SolverEnum> filtered_enums;
  for (auto se : available_solver_enums_with_generic())
  {
    if (has_all_attributes(se, attributes))
    {
      filtered_enums.push_back(se);
    }
  }
  return filtered_enums;
}

std::vector<SolverConfiguration> filter_solver_configurations_with_generic(
    const std::unordered_set<SolverAttribute> attributes)
{
  // first get the enums
  std::vector<SolverEnum> filtered_enums =
      filter_solver_enums_with_generic(attributes);

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
        filter_solver_enums_with_generic(reduced_attributes);
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

std::vector<SolverConfiguration> filter_solver_configurations(
    const std::unordered_set<SolverAttribute> attributes)
{
  std::vector<SolverConfiguration> original_result =
      filter_solver_configurations_with_generic(attributes);
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

std::string config_name(SolverConfiguration sc)
{
  std::string name = to_string(sc.solver_enum);
  if (sc.is_logging_solver)
  {
    name += "_LOGGING";
  }
  return name;
}

}  // namespace smt_tests
