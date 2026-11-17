/*!
 * \file available_solvers.h
 * \brief Convenience functions for testing
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * They collect the available solvers and filter them by solver attribute.
 */
#ifndef SMT_SWITCH_AVAILABLE_SOLVERS_H
#define SMT_SWITCH_AVAILABLE_SOLVERS_H

#include <iostream>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_set>
#include <vector>

#include "smt-switch/smt_defs.h"
#include "smt-switch/solver_enums.h"

namespace smt::tests {

/** What a backend supports, for choosing the solvers a test runs on */
enum class SolverAttribute
{
  // supports traversing terms with iteration
  TERMITER,
  // supports bit-vector theory
  THEORY_BV,
  // supports integer theory
  THEORY_INT,
  // supports real theory
  THEORY_REAL,
  // supports STR theory
  THEORY_STR,
  // supports array models
  ARRAY_MODELS,
  // supports constant arrays
  CONSTARR,
  // terms can be traversed with iteration, and a term's Op and children
  // can be used to rebuild an equivalent term in another solver
  FULL_TRANSFER,
  // supports functions with boolean arguments
  // and arrays with boolean elements
  ARRAY_FUN_BOOLS,
  // unsat core support
  UNSAT_CORE,
  // supports datatype theory
  THEORY_DATATYPE,
  // supports quantifiers
  QUANTIFIERS,
  // supports zero arity uninterpreted sorts
  UNINTERP_SORT,
  // supports non-zero arity uninterpreted sorts
  PARAM_UNINTERP_SORT,
  // supports equality and disequality between terms of an uninterpreted sort
  UNINTERP_SORT_EQ,
  // aliases booleans and bit-vectors of size one
  BOOL_BV1_ALIASING,
  // supports setting a time limit, in seconds (fractions allowed)
  TIMELIMIT
};

/** The attributes of the backend se, an interpolator sharing its solver's */
std::unordered_set<SolverAttribute> get_solver_attributes(smt::SolverEnum se);

/** Whether the backend se has the attribute sa */
bool solver_has_attribute(smt::SolverEnum se, SolverAttribute sa);

struct SolverConfiguration
{
  // fields
  smt::SolverEnum solver_enum;
  bool is_logging_solver;

  SolverConfiguration(smt::SolverEnum se, bool ils);
};

/** Creates an SmtSolver of the provided type */
smt::SmtSolver create_solver(SolverConfiguration sc);

/** The regular solver an interpolator is built on, whose theories it shares */
smt::SolverEnum interpolator_base_solver(smt::SolverEnum se);

/** The solvers create_solver can make, with GENERIC_SOLVER if the cvc5
 *  binary was found
 */
std::vector<smt::SolverEnum> available_solver_enums_with_generic();

/** The solver's own executable, or empty if configure found none */
std::string_view solver_binary(smt::SolverEnum se);

/** The available solvers, with and without logging, and GENERIC_SOLVER if
 *  the cvc5 binary was found
 */
std::vector<SolverConfiguration> available_solver_configurations_with_generic();

/** The available solvers, with and without logging */
std::vector<SolverConfiguration> available_solver_configurations();

// collect all the available interpolating solvers
std::vector<SolverConfiguration> available_interpolator_configurations();

/** Filter the available interpolating solvers by a set of attributes
 * @return all available interpolating solvers that have *all* the attributes
 */
std::vector<SolverConfiguration> filter_interpolator_configurations(
    const std::unordered_set<SolverAttribute> attributes);

/** Filter the available solvers by a set of attributes
 * @return the available solvers, GENERIC_SOLVER included, that have *all*
 *         the attributes
 */
std::vector<smt::SolverEnum> filter_solver_enums_with_generic(
    const std::unordered_set<SolverAttribute> attributes);

/** Filter the available solvers by a set of attributes
 * @return the available solver configurations, GENERIC_SOLVER included,
 *         that have *all* the attributes
 */
std::vector<SolverConfiguration> filter_solver_configurations_with_generic(
    const std::unordered_set<SolverAttribute> attributes);

/** As filter_solver_configurations_with_generic, without GENERIC_SOLVER */
std::vector<SolverConfiguration> filter_solver_configurations(
    const std::unordered_set<SolverAttribute> attributes);

std::ostream & operator<<(std::ostream & o, SolverConfiguration sc);

/** A name for a configuration that can go in a test name, e.g. CVC5 or
 *  CVC5_LOGGING
 */
std::string config_name(SolverConfiguration sc);

/** Names the cases of a suite parameterized by SolverConfiguration
 *  after their configuration, e.g.
 *    INSTANTIATE_TEST_SUITE_P(, Suite, ValuesIn(...), ConfigName());
 *  gives Suite.Test/CVC5 rather than Suite.Test/4
 */
struct ConfigName
{
  template <typename ParamInfo>
  std::string operator()(const ParamInfo & info) const
  {
    return config_name(info.param);
  }
};

/** Names the cases of a suite parameterized by a pair of
 *  SolverConfigurations after both, e.g.
 *    INSTANTIATE_TEST_SUITE_P(
 *        , Suite, Combine(ValuesIn(...), ValuesIn(...)), ConfigPairName());
 *  gives Suite.Test/CVC5_Z3 rather than Suite.Test/12
 */
struct ConfigPairName
{
  template <typename ParamInfo>
  std::string operator()(const ParamInfo & info) const
  {
    return config_name(std::get<0>(info.param)) + "_"
           + config_name(std::get<1>(info.param));
  }
};
}  // namespace smt::tests

#endif  // SMT_SWITCH_AVAILABLE_SOLVERS_H
