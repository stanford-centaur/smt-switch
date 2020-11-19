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

#include <iostream>
#include "assert.h"

using namespace std;

namespace smt {

SubstitutionWalker::SubstitutionWalker(const smt::SmtSolver & solver,
                                       const smt::UnorderedTermMap & smap)
    : solver_(solver), substitution_map(smap)
{
  // pre-populate the cache with substitutions
  for (auto elem : smap)
  {
    if (elem.first->get_sort() != elem.second->get_sort())
    {
      throw IncorrectUsageException(
          "Got bad substitution in SubstitutionWalker");
    }
    cache[elem.first] = elem.second;
  }
}

Term SubstitutionWalker::visit(smt::Term & term)
{
  TermVec to_visit({ term });
  UnorderedTermSet visited;

  Term t;
  while (to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();
    auto it = cache.find(t);
    if (it != cache.end())
    {
      // cache hit
      continue;
    }
    else if (visited.find(t) == visited.end())
    {
      visited.insert(t);
      to_visit.push_back(t);
      for (auto tt : t)
      {
        to_visit.push_back(tt);
      }
    }
    else
    {
      assert(cache.find(t) == cache.end());
      if (t->is_symbol() || t->is_value())
      {
        cache[t] = t;
      }
      else
      {
        Op op = t->get_op();
        TermVec children(t->begin(), t->end());
        assert(!op.is_null());
        assert(children.size());

        cache[t] = solver_->make_term(op, children);
      }
      assert(cache.find(t) != cache.end());
    }
  }

  for (auto elem : substitution_map)
  {
    assert(cache.at(elem.first) == elem.second);
  }

  return cache.at(term);
}

}  // namespace smt
