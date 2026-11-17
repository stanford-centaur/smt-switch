/*!
 * \file solver_enums.cpp
 * \brief Convenience functions for SolverEnums
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/solver_enums.h"

#include <sstream>

#include "smt-switch/exceptions.h"

namespace smt {

bool is_interpolator_solver_enum(SolverEnum se)
{
  return se == BZLA_INTERPOLATOR || se == CVC5_INTERPOLATOR
         || se == MSAT_INTERPOLATOR || se == YICES2_INTERPOLATOR;
}

std::ostream & operator<<(std::ostream & o, SolverEnum e)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (e)
  {
    case BTOR: return o << "BTOR";
    case BZLA: return o << "BZLA";
    case CVC5: return o << "CVC5";
    case GENERIC_SOLVER: return o << "GENERIC_SOLVER";
    case MSAT: return o << "MSAT";
    case YICES2: return o << "YICES2";
    case Z3: return o << "Z3";
    case BZLA_INTERPOLATOR: return o << "BZLA_INTERPOLATOR";
    case CVC5_INTERPOLATOR: return o << "CVC5_INTERPOLATOR";
    case MSAT_INTERPOLATOR: return o << "MSAT_INTERPOLATOR";
    case YICES2_INTERPOLATOR: return o << "YICES2_INTERPOLATOR";
  }
  throw InternalException("Unknown SolverEnum: " + std::to_string(e));
}

std::string to_string(SolverEnum e)
{
  std::ostringstream ostr;
  ostr << e;
  return ostr.str();
}

}  // namespace smt
