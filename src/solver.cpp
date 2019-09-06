#include "solver.h"

namespace smt {

// TODO: Implement a generic visitor

Term AbsSmtSolver::substitute(const Term term,
                              const UnorderedTermMap & substitution_map) const
{
  UnorderedTermMap cache;
  // populate cache with substitution map
  for (auto elem : substitution_map)
  {
    cache[elem.first] = elem.second;
  }

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

      if (cached_children.size())
      {
        cache[t] = make_term(t->get_op(), cached_children);
      }
    }
  }

  return cache.at(term);
}

}  // namespace smt
