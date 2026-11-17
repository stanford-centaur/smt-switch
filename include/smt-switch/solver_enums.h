/*!
 * \file solver_enums.h
 * \brief Enums for identifying SmtSolver objects
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_SOLVER_ENUMS_H
#define SMT_SWITCH_SOLVER_ENUMS_H

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#include <ostream>
#include <string>

namespace smt {
enum SolverEnum
{
  BTOR = 0,        // boolector
  BZLA,            // bitwuzla
  CVC5,            // cvc5
  GENERIC_SOLVER,  // generic solver (binary)
  MSAT,            // mathsat
  YICES2,          // yices2
  Z3,              // z3

  // interpolating solvers -- note these cannot be logging solvers
  // because the solver takes the initiative in creating the interpolant
  // so there's no way to keep a DAG at the smt-switch level
  BZLA_INTERPOLATOR,
  CVC5_INTERPOLATOR,
  MSAT_INTERPOLATOR,
  YICES2_INTERPOLATOR,

  // NOTE: when adding a new enum, also add it to the python interface, in
  // python/smt_switch/cppenums.pxd and python/smt_switch/solverenums.pyx
};

/** Returns true iff the SolverEnum corresponds to an Interpolator
 *  @param se the solver enum to check
 *  @return true iff the se is a *_INTERPOLATOR enum
 */
bool is_interpolator_solver_enum(SolverEnum se);

std::ostream & operator<<(std::ostream & o, SolverEnum e);

std::string to_string(SolverEnum e);

}  // namespace smt

#endif  // SMT_SWITCH_SOLVER_ENUMS_H
