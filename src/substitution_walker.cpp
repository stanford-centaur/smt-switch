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

#include "substitution_walker.h"

namespace smt {

SubstitutionWalker::SubstitutionWalker(
    const smt::SmtSolver & solver,
    const smt::UnorderedTermMap & substitution_map)
    : IdentityWalker(solver, false)
{
  // pre-populate the cache with substitutions
  for (auto elem : substitution_map)
  {
    if (elem.first->get_sort() != elem.second->get_sort())
    {
      throw IncorrectUsageException("Got mismatch in sorts for substitution: "
                                    + elem.first->to_string() + ":"
                                    + elem.first->get_sort()->to_string() + " "
                                    + elem.second->to_string() + ":"
                                    + elem.second->get_sort()->to_string());
    }
    save_in_cache(elem.first, elem.second);
  }
}
}  // namespace smt
