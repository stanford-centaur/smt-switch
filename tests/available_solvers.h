#pragma once

#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "smt_defs.h"

namespace smt_tests {

enum SolverEnum
{
  BTOR = 0,
  CVC4,
  MSAT,
  YICES2,
  // have separate enum for solver wrapped by LoggingSolver with Shadow DAG
  // test all versions of that also
  BTOR_LOGGING,
  CVC4_LOGGING,
  MSAT_LOGGING,
  YICES2_LOGGING
};

enum SolverAttribute
{
  // this enum is wrapped by a LoggingSolver
  LOGGING = 0,
  // supports traversing terms with iteration
  TERMITER,
  // supports integer theory
  THEORY_INT,
  // supports array models
  ARRAY_MODELS,
  // supports constant arrays
  CONSTARR,
  // supports transferring to different solvers with TermTranslator
  FULL_TRANSFER,
  // unsat core support
  UNSAT_CORE,
};

/** Creates an SmtSolver of the provided type */
smt::SmtSolver create_solver(SolverEnum se);

/** Creates an interpolating SmtSolver of the provided type */
smt::SmtSolver create_interpolating_solver(SolverEnum se);

// collect all the available solvers
std::vector<SolverEnum> available_solver_enums();

// collect all the available non-logging solvers
std::vector<SolverEnum> available_no_logging_solver_enums();

// collect all the available logging solvers
std::vector<SolverEnum> available_logging_solver_enums();

// collect all the available interpolating solvers
std::vector<SolverEnum> available_interpolator_enums();

/** Filter the available solvers by a set of attributes
 * @return all available solvers that have *all* the attributes
 */
std::vector<SolverEnum> filter_solver_enums(
    const std::unordered_set<SolverAttribute> attributes);

std::ostream & operator<<(std::ostream & o, SolverEnum e);

}  // namespace smt_tests

// define hash for older compilers
namespace std {
// specialize template
template <>
struct hash<smt_tests::SolverEnum>
{
  size_t operator()(const smt_tests::SolverEnum se) const
  {
    return static_cast<size_t>(se);
  }
};

// specialize template
 template <>
   struct hash<smt_tests::SolverAttribute>
 {
   size_t operator()(const smt_tests::SolverAttribute sa) const
   {
     return static_cast<size_t>(sa);
   }
 };

}  // namespace std
