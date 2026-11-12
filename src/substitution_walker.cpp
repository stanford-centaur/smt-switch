/*!
 * \file substitution_walker.cpp
 * \brief Substitution walker for doing substitutions with a persistent cache
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/substitution_walker.h"

#include <memory>
#include <string>
#include <utility>

#include "smt-switch/exceptions.h"
#include "smt-switch/sort.h"

namespace smt {

SubstitutionWalker::SubstitutionWalker(
    const SmtSolver & solver, const UnorderedTermMap & substitution_map)
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

SubstitutionWalker::~SubstitutionWalker() = default;
}  // namespace smt
