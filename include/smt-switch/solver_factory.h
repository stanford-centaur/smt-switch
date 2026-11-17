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

namespace solvers {

/** Create a solver
 *  @param se the solver, which must not be an interpolator or
 *         GENERIC_SOLVER (construct a GenericSolver for that)
 *  @param logging if true, wraps the solver in a LoggingSolver
 *  @return the new solver
 *  @throws IncorrectUsageException for an interpolator or GENERIC_SOLVER
 *  @throws NotImplementedException if the backend is not available
 *  @throws SystemException if the backend is installed but cannot be loaded
 */
SmtSolver create(SolverEnum se, bool logging);

/** The solvers create can create
 *  @throws SystemException if a backend is installed but cannot be loaded
 */
std::vector<SolverEnum> available();

}  // namespace solvers

namespace interpolators {

/** Create an interpolator
 *  @param se the interpolator, such as CVC5_INTERPOLATOR
 *  @return the new interpolator
 *  @throws IncorrectUsageException for a solver enum that is not an
 *          interpolator
 *  @throws NotImplementedException if the backend is not available or
 *          cannot interpolate
 *  @throws SystemException if the backend is installed but cannot be loaded
 */
SmtInterpolator create(SolverEnum se);

/** The interpolators create can create
 *  @throws SystemException if a backend is installed but cannot be loaded
 */
std::vector<SolverEnum> available();

}  // namespace interpolators

namespace backend {

/** What a backend library provides for solvers::create and
 *  interpolators::create
 */
struct Factory
{
  SmtSolver (*create)(bool logging);
  /** Null for a backend that cannot interpolate */
  SmtInterpolator (*create_interpolator)();
};

// Each backend library defines its own, under these names, which the
// loader looks up.
extern "C" {
extern const Factory smt_switch_backend_bitwuzla;
extern const Factory smt_switch_backend_btor;
extern const Factory smt_switch_backend_cvc5;
extern const Factory smt_switch_backend_msat;
extern const Factory smt_switch_backend_yices2;
extern const Factory smt_switch_backend_z3;
}

}  // namespace backend

}  // namespace smt

#endif  // SMT_SWITCH_SOLVER_FACTORY_H
