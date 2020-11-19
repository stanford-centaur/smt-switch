/*********************                                                        */
/*! \file substitution_walker.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Substitution walker for doing substitutions with a persistent cache
**
**/

#pragma once

#include "exceptions.h"
#include "smt.h"

namespace smt {
// class for doing substitutions
// can be more efficient than SmtSolver::substitute if it
// is called repeatedly since it has a persistent cache
// NOTE: don't even need to override visit_term
//       just need to prepulate the cache
class SubstitutionWalker
{
 public:
  SubstitutionWalker(const smt::SmtSolver & solver,
                     const smt::UnorderedTermMap & smap);

  smt::Term visit(smt::Term & term);

 protected:
  const smt::SmtSolver & solver_; /**< the solver to use for rebuilding terms */
  UnorderedTermMap substitution_map;
  UnorderedTermMap cache;
};
}  // namespace smt
