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

#include "identity_walker.h"
#include "smt_defs.h"
#include "term.h"

namespace smt {
// class for doing substitutions
// can more efficient than SmtSolver::substitute if it
// is called repeatedly since it has a persistent cache
// NOTE: don't even need to override visit_term
//       just need to prepulate the cache
class SubstitutionWalker : public IdentityWalker
{
 public:
  SubstitutionWalker(const SmtSolver & solver, const UnorderedTermMap & smap);
};
}  // namespace smt
