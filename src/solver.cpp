/*********************                                                        */
/*! \file solver.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Abstract interface for SMT solvers.
**
**
**/

#include "solver.h"

#include "exceptions.h"

namespace smt {

// TODO: Implement a generic visitor

Term AbsSmtSolver::substitute(const Term term,
                              const UnorderedTermMap & substitution_map) const
{
  // cache starts with the substitutions
  UnorderedTermMap cache(substitution_map);
  TermVec to_visit{ term };
  TermVec cached_children;
  Term t;
  while (to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();
    if (cache.find(t) == cache.end())
    {
      // doesn't get updated yet, just marking as visited
      cache[t] = t;
      to_visit.push_back(t);
      for (auto c : t)
      {
        to_visit.push_back(c);
      }
    }
    else
    {
      cached_children.clear();
      for (auto c : t)
      {
        cached_children.push_back(cache.at(c));
      }

      // const arrays have children but don't need to be rebuilt
      // (they're constructed in a particular way anyway)
      if (cached_children.size() && !t->is_value())
      {
        cache[t] = make_term(t->get_op(), cached_children);
      }
    }
  }

  return cache.at(term);
}

TermVec AbsSmtSolver::substitute_terms(
    const TermVec & terms, const UnorderedTermMap & substitution_map) const
{
  TermVec res;
  res.reserve(terms.size());
  for (auto t : terms)
  {
    res.push_back(substitute(t, substitution_map));
  }
  return res;
}

}  // namespace smt
