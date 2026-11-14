/*!
 * \file solver_factory.h
 * \brief Creating a solver or interpolator from its solver enum
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Each backend also has its own factory, such as Cvc5SolverFactory. These
 * functions reach any backend through its enum, so a program can choose a
 * solver at run time. A backend is found if the program links it or if it
 * is installed beside libsmt-switch.
 */
#ifndef SMT_SWITCH_SOLVER_FACTORY_H
#define SMT_SWITCH_SOLVER_FACTORY_H

#include <vector>

#include "smt-switch/smt_defs.h"
#include "smt-switch/solver_enums.h"

namespace smt {

/** Create a solver
 *  @param se the solver, which must not be an interpolator or
 *         GENERIC_SOLVER (construct a GenericSolver for that)
 *  @param logging if true, wraps the solver in a LoggingSolver
 *  @return the new solver
 *  @throws IncorrectUsageException for an interpolator or GENERIC_SOLVER
 *  @throws NotImplementedException if the backend is not available
 *  @throws SystemException if the backend is installed but cannot be loaded
 */
SmtSolver create_solver(SolverEnum se, bool logging);

/** Create an interpolator
 *  @param se the interpolator, such as CVC5_INTERPOLATOR
 *  @return the new interpolator
 *  @throws IncorrectUsageException for a solver enum that is not an
 *          interpolator
 *  @throws NotImplementedException if the backend is not available or
 *          cannot interpolate
 *  @throws SystemException if the backend is installed but cannot be loaded
 */
SmtInterpolator create_interpolator(SolverEnum se);

/** The solvers create_solver can create
 *  @throws SystemException if a backend is installed but cannot be loaded
 */
std::vector<SolverEnum> available_solver_enums();

/** The interpolators create_interpolator can create
 *  @throws SystemException if a backend is installed but cannot be loaded
 */
std::vector<SolverEnum> available_interpolator_enums();

namespace detail {

/** What a backend library provides for create_solver and
 *  create_interpolator
 */
struct BackendFactory
{
  SmtSolver (*create)(bool logging);
  /** Null for a backend that cannot interpolate */
  SmtInterpolator (*create_interpolator)();
};

// Each backend library defines its own, under these names, which the
// loader looks up.
extern "C" {
extern const BackendFactory smt_switch_backend_bitwuzla;
extern const BackendFactory smt_switch_backend_btor;
extern const BackendFactory smt_switch_backend_cvc5;
extern const BackendFactory smt_switch_backend_msat;
extern const BackendFactory smt_switch_backend_yices2;
extern const BackendFactory smt_switch_backend_z3;
}

}  // namespace detail

}  // namespace smt

#endif  // SMT_SWITCH_SOLVER_FACTORY_H
