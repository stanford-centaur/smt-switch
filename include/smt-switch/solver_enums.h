/*!
 * \file solver_enums.h
 * \brief Enums identifying the backend of a solver or interpolator
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

namespace solvers {

/** The backend of a solver
 *  When adding one, also add it to the Python bindings, in
 *  python/smt_switch/cppenums.pxd and python/smt_switch/solverkinds.pyx.
 */
enum Kind
{
  BTOR,
  BZLA,
  CVC5,
  GENERIC,
  MSAT,
  YICES2,
  Z3
};

std::ostream & operator<<(std::ostream & o, Kind kind);

std::string to_string(Kind kind);

}  // namespace solvers

namespace interpolators {

/** The backend of an interpolator
 *  When adding one, also add it to the Python bindings, in
 *  python/smt_switch/cppenums.pxd and python/smt_switch/interpolatorkinds.pyx.
 */
enum Kind
{
  BZLA,
  CVC5,
  MSAT,
  YICES2
};

/** @return the kind of the solver that builds the terms of an interpolator
 *          of the given kind
 */
solvers::Kind solver_kind(Kind kind);

std::ostream & operator<<(std::ostream & o, Kind kind);

std::string to_string(Kind kind);

}  // namespace interpolators

}  // namespace smt

#endif  // SMT_SWITCH_SOLVER_ENUMS_H
