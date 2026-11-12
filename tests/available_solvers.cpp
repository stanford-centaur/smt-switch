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
#include "smt-switch/logging_solver.h"
#include "test_paths.h"

#ifdef BUILD_BTOR
#include "smt-switch/boolector_factory.h"
#endif

#ifdef BUILD_BITWUZLA
#include "smt-switch/bitwuzla_factory.h"
#endif

#ifdef BUILD_CVC5
#include "smt-switch/cvc5_factory.h"
#include "smt-switch/generic_solver.h"
#endif

#ifdef BUILD_MSAT
#include "smt-switch/msat_factory.h"
#endif

#ifdef BUILD_YICES2
#include "smt-switch/yices2_factory.h"
#endif

#ifdef BUILD_Z3
#include "smt-switch/z3_factory.h"
#endif

using namespace smt;

namespace smt_tests {

SolverConfiguration::SolverConfiguration(smt::SolverKind kind, bool ils)
    : solver_kind(kind), is_logging_solver(ils)
{
}

SmtSolver create_solver(SolverConfiguration sc)
{
  // Every kind has a case, so -Wswitch flags a new one; a solver this build
  // leaves out breaks out to the throw below.
  switch (sc.solver_kind)
  {
    case SolverKind::BTOR:
#ifdef BUILD_BTOR
      return BoolectorSolverFactory::create(sc.is_logging_solver);
#else
      break;
#endif
    case SolverKind::BZLA:
#ifdef BUILD_BITWUZLA
      return BitwuzlaSolverFactory::create(sc.is_logging_solver);
#else
      break;
#endif
    case SolverKind::CVC5:
#ifdef BUILD_CVC5
      return Cvc5SolverFactory::create(sc.is_logging_solver);
#else
      break;
#endif
    case SolverKind::GENERIC: {
#ifdef BUILD_CVC5
      std::string path(solver_binary(SolverKind::CVC5));
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
      else
      {
        return std::make_shared<GenericSolver>(path, args, response_timeout, 5);
      }
#else
      break;
#endif
    }
    case SolverKind::MSAT:
#ifdef BUILD_MSAT
      return MsatSolverFactory::create(sc.is_logging_solver);
#else
      break;
#endif
    case SolverKind::YICES2:
#ifdef BUILD_YICES2
      return Yices2SolverFactory::create(sc.is_logging_solver);
#else
      break;
#endif
    case SolverKind::Z3:
#ifdef BUILD_Z3
      return Z3SolverFactory::create(sc.is_logging_solver);
#else
      break;
#endif
  }
  throw SmtException("Solver " + to_string(sc.solver_kind) + " is not built");
}

SmtInterpolator create_interpolator(InterpolatorKind itp_kind)
{
  // Every kind has a case, so -Wswitch flags a new one; an interpolator this
  // build leaves out breaks out to the throw below.
  switch (itp_kind)
  {
    case InterpolatorKind::BZLA:
#ifdef BUILD_BITWUZLA
      return BitwuzlaSolverFactory::create_interpolator();
#else
      break;
#endif
    case InterpolatorKind::CVC5:
#ifdef BUILD_CVC5
      return Cvc5SolverFactory::create_interpolator();
#else
      break;
#endif
    case InterpolatorKind::MSAT:
#ifdef BUILD_MSAT
      return MsatSolverFactory::create_interpolator();
#else
      break;
#endif
    case InterpolatorKind::YICES2:
#ifdef BUILD_YICES2
      return Yices2SolverFactory::create_interpolator();
#else
      break;
#endif
  }
  throw SmtException("Interpolator " + to_string(itp_kind) + " is not built");
}

std::vector<SolverKind> available_solver_kinds()
{
  std::vector<SolverKind> kinds = {
#ifdef BUILD_BTOR
    SolverKind::BTOR,
#endif
#ifdef BUILD_BITWUZLA
    SolverKind::BZLA,
#endif
#ifdef BUILD_CVC5
    SolverKind::CVC5,
#endif
#ifdef BUILD_MSAT
    SolverKind::MSAT,
#endif
#ifdef BUILD_YICES2
    SolverKind::YICES2,
#endif
#ifdef BUILD_Z3
    SolverKind::Z3,
#endif
  };
  // the generic solver drives the cvc5 executable
  if (!solver_binary(SolverKind::CVC5).empty())
  {
    kinds.push_back(SolverKind::GENERIC);
  }
  return kinds;
}

std::string_view solver_binary(SolverKind solver_kind)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (solver_kind)
  {
    case SolverKind::BTOR: return smt_tests::boolector_binary;
    case SolverKind::BZLA: return smt_tests::bitwuzla_binary;
    case SolverKind::CVC5: return smt_tests::cvc5_binary;
    case SolverKind::MSAT: return smt_tests::mathsat_binary;
    case SolverKind::YICES2: return smt_tests::yices2_binary;
    case SolverKind::Z3: return smt_tests::z3_binary;
    // the generic solver drives another solver's executable
    case SolverKind::GENERIC: break;
  }
  return "";
}

std::vector<SolverKind> available_non_generic_solver_kinds()
{
  std::vector<SolverKind> result;
  for (SolverKind solver_kind : available_solver_kinds())
  {
    if (solver_kind != SolverKind::GENERIC)
    {
      result.push_back(solver_kind);
    }
  }
  return result;
}

std::vector<SolverConfiguration> available_solver_configurations()
{
  std::vector<SolverConfiguration> configs;
  for (SolverKind solver_kind : available_solver_kinds())
  {
    SolverConfiguration sct(solver_kind, true);
    SolverConfiguration scf(solver_kind, false);
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
    if (sc.solver_kind != SolverKind::GENERIC)
    {
      result.push_back(sc);
    }
  }
  return result;
}

std::vector<InterpolatorKind> available_interpolator_kinds()
{
  std::vector<InterpolatorKind> result;
#ifdef SMT_SWITCH_BITWUZLA_HAS_INTERPOLANTS
  result.push_back(InterpolatorKind::BZLA);
#endif
#ifdef BUILD_CVC5
  result.push_back(InterpolatorKind::CVC5);
#endif
#ifdef BUILD_MSAT
  result.push_back(InterpolatorKind::MSAT);
#endif
#ifdef BUILD_YICES2
  // a Yices2 without MCSAT refuses to create an interpolator
  try
  {
    Yices2SolverFactory::create_interpolator();
    result.push_back(InterpolatorKind::YICES2);
  }
  catch (const NotImplementedException &)
  {
  }
#endif
  return result;
}

namespace {

/** Whether solver_kind has every one of the attributes */
bool has_all_attributes(SolverKind solver_kind,
                        const std::unordered_set<SolverAttribute> & attributes)
{
  const std::unordered_set<SolverAttribute> sk_attrs =
      get_solver_attributes(solver_kind);
  return std::all_of(
      attributes.begin(), attributes.end(), [&sk_attrs](SolverAttribute a) {
        return sk_attrs.find(a) != sk_attrs.end();
      });
}

}  // namespace

std::vector<InterpolatorKind> filter_interpolator_kinds(
    const std::unordered_set<SolverAttribute> attributes)
{
  std::vector<InterpolatorKind> result;
  for (InterpolatorKind itp_kind : available_interpolator_kinds())
  {
    if (has_all_attributes(solver_kind(itp_kind), attributes))
    {
      result.push_back(itp_kind);
    }
  }
  return result;
}

std::vector<SolverKind> filter_solver_kinds(
    const std::unordered_set<SolverAttribute> attributes)
{
  std::vector<SolverKind> filtered_kinds;
  for (auto solver_kind : available_solver_kinds())
  {
    if (has_all_attributes(solver_kind, attributes))
    {
      filtered_kinds.push_back(solver_kind);
    }
  }
  return filtered_kinds;
}

std::vector<SolverConfiguration> filter_solver_configurations(
    const std::unordered_set<SolverAttribute> attributes)
{
  // first get the kinds
  std::vector<SolverKind> filtered_kinds = filter_solver_kinds(attributes);

  // compute result
  std::vector<SolverConfiguration> result;
  for (SolverKind solver_kind : filtered_kinds)
  {
    SolverConfiguration scf(solver_kind, false);
    SolverConfiguration sct(solver_kind, true);
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
    // get filtered kinds for the rest of the attributes
    std::vector<SolverKind> reduced_filtered_kinds =
        filter_solver_kinds(reduced_attributes);
    std::unordered_set<SolverKind> filtered_kinds_set(filtered_kinds.begin(),
                                                      filtered_kinds.end());
    for (auto solver_kind : reduced_filtered_kinds)
    {
      if (filtered_kinds_set.find(solver_kind) == filtered_kinds_set.end())
      {
        result.push_back(SolverConfiguration(solver_kind, true));
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
    if (sc.solver_kind != SolverKind::GENERIC)
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

}  // namespace smt_tests
