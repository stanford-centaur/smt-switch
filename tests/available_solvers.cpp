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

namespace smt::tests {

SolverConfiguration::SolverConfiguration(solvers::Kind kind, bool ils)
    : solver_kind(kind), is_logging_solver(ils)
{
}

SmtSolver create_solver(SolverConfiguration sc)
{
  if (sc.solver_kind != solvers::GENERIC)
  {
    return solvers::create(sc.solver_kind, sc.is_logging_solver);
  }
  std::string path(solver_binary(solvers::CVC5));
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

bool solver_has_attribute(solvers::Kind kind, SolverAttribute sa)
{
  std::unordered_set<SolverAttribute> solver_attrs =
      get_solver_attributes(kind);
  return solver_attrs.find(sa) != solver_attrs.end();
}

std::unordered_set<SolverAttribute> get_solver_attributes(solvers::Kind kind)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (kind)
  {
    // Boolector throws on a positive equality between two different
    // constant arrays that its preprocessing cannot remove.
    case solvers::BTOR:
      return {
        SolverAttribute::TERMITER,          SolverAttribute::ARRAY_MODELS,
        SolverAttribute::THEORY_BV,         SolverAttribute::CONSTARR,
        SolverAttribute::UNSAT_CORE,        SolverAttribute::QUANTIFIERS,
        SolverAttribute::BOOL_BV1_ALIASING, SolverAttribute::TIMELIMIT
      };
    // Bitwuzla answers unknown to an equality between terms of an
    // uninterpreted sort that its preprocessing cannot remove.
    case solvers::BZLA:
      return {
        SolverAttribute::TERMITER,           SolverAttribute::ARRAY_MODELS,
        SolverAttribute::CONSTARR,           SolverAttribute::CONSTARR_EQ,
        SolverAttribute::FULL_TRANSFER,      SolverAttribute::UNSAT_CORE,
        SolverAttribute::THEORY_BV,          SolverAttribute::QUANTIFIERS,
        SolverAttribute::TIMELIMIT,          SolverAttribute::UNINTERP_SORT,
        SolverAttribute::PARAM_UNINTERP_SORT
      };
    // cvc5 throws on an equality between stores over two different constant
    // arrays.
    case solvers::CVC5:
      return {
        SolverAttribute::TERMITER,         SolverAttribute::THEORY_INT,
        SolverAttribute::THEORY_STR,       SolverAttribute::THEORY_BV,
        SolverAttribute::THEORY_REAL,      SolverAttribute::ARRAY_MODELS,
        SolverAttribute::ARRAY_FUN_BOOLS,  SolverAttribute::CONSTARR,
        SolverAttribute::FULL_TRANSFER,    SolverAttribute::UNSAT_CORE,
        SolverAttribute::THEORY_DATATYPE,  SolverAttribute::QUANTIFIERS,
        SolverAttribute::UNINTERP_SORT,    SolverAttribute::PARAM_UNINTERP_SORT,
        SolverAttribute::UNINTERP_SORT_EQ, SolverAttribute::TIMELIMIT
      };
    case solvers::GENERIC:
      return { SolverAttribute::TERMITER,
               SolverAttribute::ARRAY_MODELS,
               SolverAttribute::THEORY_INT,
               SolverAttribute::THEORY_BV,
               SolverAttribute::THEORY_REAL,
               SolverAttribute::ARRAY_FUN_BOOLS,
               SolverAttribute::UNSAT_CORE,
               SolverAttribute::THEORY_DATATYPE,
               SolverAttribute::QUANTIFIERS,
               SolverAttribute::UNINTERP_SORT,
               SolverAttribute::PARAM_UNINTERP_SORT,
               SolverAttribute::UNINTERP_SORT_EQ };
    case solvers::MSAT:
      return { SolverAttribute::TERMITER,
               SolverAttribute::THEORY_INT,
               SolverAttribute::THEORY_BV,
               SolverAttribute::THEORY_REAL,
               SolverAttribute::ARRAY_MODELS,
               SolverAttribute::CONSTARR,
               SolverAttribute::CONSTARR_EQ,
               SolverAttribute::FULL_TRANSFER,
               SolverAttribute::UNSAT_CORE,
               SolverAttribute::UNINTERP_SORT,
               SolverAttribute::PARAM_UNINTERP_SORT,
               SolverAttribute::UNINTERP_SORT_EQ,
               SolverAttribute::TIMELIMIT };
    // Yices2 builds a constant array as a lambda, which its context refuses
    // unless preprocessing removes it, as it does not for a store over one.
    case solvers::YICES2:
      return {
        SolverAttribute::FULL_TRANSFER,       SolverAttribute::TERMITER,
        SolverAttribute::THEORY_INT,          SolverAttribute::THEORY_BV,
        SolverAttribute::THEORY_REAL,         SolverAttribute::ARRAY_FUN_BOOLS,
        SolverAttribute::ARRAY_MODELS,        SolverAttribute::UNINTERP_SORT,
        SolverAttribute::PARAM_UNINTERP_SORT, SolverAttribute::UNINTERP_SORT_EQ,
        SolverAttribute::TIMELIMIT,           SolverAttribute::UNSAT_CORE
      };
    case solvers::Z3:
      return {
        SolverAttribute::TERMITER,         SolverAttribute::THEORY_INT,
        SolverAttribute::THEORY_BV,        SolverAttribute::THEORY_REAL,
        SolverAttribute::ARRAY_FUN_BOOLS,  SolverAttribute::ARRAY_MODELS,
        SolverAttribute::CONSTARR,         SolverAttribute::CONSTARR_EQ,
        SolverAttribute::FULL_TRANSFER,    SolverAttribute::UNSAT_CORE,
        SolverAttribute::THEORY_DATATYPE,  SolverAttribute::QUANTIFIERS,
        SolverAttribute::UNINTERP_SORT,    SolverAttribute::PARAM_UNINTERP_SORT,
        SolverAttribute::UNINTERP_SORT_EQ, SolverAttribute::TIMELIMIT
      };
  }
  throw InternalException("Unknown solver kind: " + to_string(kind));
}

std::vector<solvers::Kind> available_solver_kinds_with_generic()
{
  std::vector<solvers::Kind> kinds = solvers::available();
  // the generic solver drives the cvc5 executable
  if (!solver_binary(solvers::CVC5).empty())
  {
    kinds.push_back(solvers::GENERIC);
  }
  return kinds;
}

std::string_view solver_binary(solvers::Kind kind)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (kind)
  {
    case solvers::BTOR: return boolector_binary;
    case solvers::BZLA: return bitwuzla_binary;
    case solvers::CVC5: return cvc5_binary;
    case solvers::MSAT: return mathsat_binary;
    case solvers::YICES2: return yices2_binary;
    case solvers::Z3: return z3_binary;
    // the generic solver drives another solver's executable
    case solvers::GENERIC: break;
  }
  return "";
}

std::vector<SolverConfiguration> available_solver_configurations_with_generic()
{
  std::vector<SolverConfiguration> configs;
  for (solvers::Kind kind : available_solver_kinds_with_generic())
  {
    SolverConfiguration sct(kind, true);
    SolverConfiguration scf(kind, false);
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
    if (sc.solver_kind != solvers::GENERIC)
    {
      result.push_back(sc);
    }
  }
  return result;
}

namespace {

/** Whether kind has every one of the attributes */
bool has_all_attributes(solvers::Kind kind,
                        const std::unordered_set<SolverAttribute> & attributes)
{
  const std::unordered_set<SolverAttribute> kind_attrs =
      get_solver_attributes(kind);
  return std::all_of(
      attributes.begin(), attributes.end(), [&kind_attrs](SolverAttribute a) {
        return kind_attrs.find(a) != kind_attrs.end();
      });
}

}  // namespace

std::vector<interpolators::Kind> filter_interpolator_kinds(
    const std::unordered_set<SolverAttribute> attributes)
{
  std::vector<interpolators::Kind> result;
  for (interpolators::Kind kind : interpolators::available())
  {
    if (has_all_attributes(interpolators::solver_kind(kind), attributes))
    {
      result.push_back(kind);
    }
  }
  return result;
}

std::vector<solvers::Kind> filter_solver_kinds_with_generic(
    const std::unordered_set<SolverAttribute> attributes)
{
  std::vector<solvers::Kind> filtered_kinds;
  for (auto kind : available_solver_kinds_with_generic())
  {
    if (has_all_attributes(kind, attributes))
    {
      filtered_kinds.push_back(kind);
    }
  }
  return filtered_kinds;
}

std::vector<SolverConfiguration> filter_solver_configurations_with_generic(
    const std::unordered_set<SolverAttribute> attributes)
{
  // first get the kinds
  std::vector<solvers::Kind> filtered_kinds =
      filter_solver_kinds_with_generic(attributes);

  // compute result
  std::vector<SolverConfiguration> result;
  for (solvers::Kind kind : filtered_kinds)
  {
    SolverConfiguration scf(kind, false);
    SolverConfiguration sct(kind, true);
    result.push_back(scf);
    result.push_back(sct);
  }

  // there are some features that logging solvers support even if the base
  // solver does not
  if (attributes.find(SolverAttribute::TERMITER) != attributes.end()
      || attributes.find(SolverAttribute::FULL_TRANSFER) != attributes.end())
  {
    std::unordered_set<SolverAttribute> reduced_attributes = attributes;
    reduced_attributes.erase(SolverAttribute::TERMITER);
    reduced_attributes.erase(SolverAttribute::FULL_TRANSFER);
    // get filtered kinds for the rest of the attributes
    std::vector<solvers::Kind> reduced_filtered_kinds =
        filter_solver_kinds_with_generic(reduced_attributes);
    std::unordered_set<solvers::Kind> filtered_kinds_set(filtered_kinds.begin(),
                                                         filtered_kinds.end());
    for (auto kind : reduced_filtered_kinds)
    {
      if (filtered_kinds_set.find(kind) == filtered_kinds_set.end())
      {
        result.push_back(SolverConfiguration(kind, true));
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
    if (sc.solver_kind != solvers::GENERIC)
    {
      result.push_back(sc);
    }
  }
  return result;
}

std::ostream & operator<<(std::ostream & o, SolverConfiguration sc)
{
  o << sc.solver_kind << "(logging=" << sc.is_logging_solver << ")";
  return o;
}

std::string config_name(SolverConfiguration sc)
{
  std::string name = to_string(sc.solver_kind);
  if (sc.is_logging_solver)
  {
    name += "_LOGGING";
  }
  return name;
}

}  // namespace smt::tests
