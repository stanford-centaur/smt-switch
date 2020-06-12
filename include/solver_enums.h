/*********************                                                        */
/*! \file solver_enums.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Enums for identifying SmtSolver objects
**
**
**/
#pragma once

#include <unordered_set>

namespace smt {
enum SolverEnum
{
  BTOR = 0,
  CVC4,
  MSAT,
  YICES2,
  // have separate enum for solver wrapped by LoggingSolver with Shadow DAG
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
  // supports datatype theory
  THEORY_DATATYPE,
};

/** Returns true iff the SolverEnum corresponds to a LoggingSolver
 *  @param se the solver enum to check
 *  @return true iff the se is a *_LOGGING enum
 */
bool is_logging(SolverEnum se);

/** Maps a non-logging solver enum to the logging version
 *  e.g. BTOR -> BTOR_LOGGING
 *  @param se a non-logging solver enum to map
 *  @return the logging solver version of this enum
 */
SolverEnum get_logging_solver_enum(SolverEnum se);

bool solver_has_attribute(SolverEnum se, SolverAttribute sa);

std::unordered_set<SolverAttribute> get_solver_attributes(SolverEnum se);

std::ostream & operator<<(std::ostream & o, SolverEnum e);

std::string to_string(SolverEnum e);

}  // namespace smt

// define hash for older compilers
namespace std {
// specialize template
template <>
struct hash<smt::SolverEnum>
{
  size_t operator()(const smt::SolverEnum se) const
  {
    return static_cast<size_t>(se);
  }
};

// specialize template
template <>
struct hash<smt::SolverAttribute>
{
  size_t operator()(const smt::SolverAttribute sa) const
  {
    return static_cast<size_t>(sa);
  }
};

}  // namespace std
