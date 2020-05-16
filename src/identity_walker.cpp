/*********************                                                        */
/*! \file identity_walker.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Identity walker class that can be inherited and modified for
**        term traversal and manipulation.
**
**/

#include "identity_walker.h"

using namespace smt;
using namespace std;

namespace smt
{

Term IdentityWalker::visit(Term & term)
{
  if (clear_cache_)
  {
    cache_.clear();
  }

  TermVec to_visit({term});
  // Note: visited is different than cache keys
  //       might want to visit without saving to the cache
  //       and if something is in the cache it wouldn't
  //       visit it again (e.g. in post-order traversal)
  UnorderedTermSet visited;

  Term t;
  WalkerStepResult res;
  while(to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();

    if (cache_.find(t) != cache_.end())
    {
      // cache hit
      continue;
    }

    // in preorder if it has not been seen before
    preorder_ = (visited.find(t) == visited.end());
    // add to visited after determining whether we're in the pre-
    // or post-order
    visited.insert(t);
    res = visit_term(t);

    if (res == Walker_Abort)
    {
      if (cache_.find(term) != cache_.end())
      {
        return cache_.at(term);
      }
      return term;
    }

    if (preorder_)
    {
      if (res == Walker_Continue)
      {
        to_visit.push_back(t);
        for (auto tt : t)
        {
          to_visit.push_back(tt);
        }
      }
    }
  }


  if (cache_.find(term) == cache_.end())
  {
    return term;
  }
  else
  {
    return cache_.at(term);
  }
}

WalkerStepResult IdentityWalker::visit_term(Term & term)
{
  if (!preorder_)
  {
    Op op = term->get_op();
    if (!op.is_null())
    {
      TermVec cached_children;
      for (auto t : term)
      {
        cached_children.push_back(cache_.at(t));
      }
      cache_[term] = solver_->make_term(op, cached_children);
    }
    else
    {
      // just keep the leaves the same
      cache_[term] = term;
    }
  }

  return Walker_Continue;
}

}
