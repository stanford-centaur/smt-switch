/*!
 * \file solver_enums.cpp
 * \brief Printing and converting the solver and interpolator kinds
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/solver_enums.h"

#include <sstream>
#include <string>

#include "smt-switch/exceptions.h"

namespace smt {

namespace solvers {

std::ostream & operator<<(std::ostream & o, Kind kind)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (kind)
  {
    case BTOR: return o << "BTOR";
    case BZLA: return o << "BZLA";
    case CVC5: return o << "CVC5";
    case GENERIC: return o << "GENERIC";
    case MSAT: return o << "MSAT";
    case YICES2: return o << "YICES2";
    case Z3: return o << "Z3";
  }
  throw InternalException("Unknown solver kind: " + std::to_string(kind));
}

std::string to_string(Kind kind)
{
  std::ostringstream ostr;
  ostr << kind;
  return ostr.str();
}

}  // namespace solvers

namespace interpolators {

solvers::Kind solver_kind(Kind kind)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (kind)
  {
    case BZLA: return solvers::BZLA;
    case CVC5: return solvers::CVC5;
    case MSAT: return solvers::MSAT;
    case YICES2: return solvers::YICES2;
  }
  throw InternalException("Unknown interpolator kind: " + std::to_string(kind));
}

std::ostream & operator<<(std::ostream & o, Kind kind)
{
  return o << solver_kind(kind);
}

std::string to_string(Kind kind)
{
  std::ostringstream ostr;
  ostr << kind;
  return ostr.str();
}

}  // namespace interpolators

}  // namespace smt
