#include "tree_walker.h"

using namespace smt;
using namespace std;

namespace smt
{

Term TreeWalker::visit(pair <Term, vector<int>> & occurrence)
{
  if (clear_cache_)
  {
    cache_.clear();

    if (ext_cache_)
    {
      ext_cache_->clear();
    }
  }

  Term out = occurrence;
  if (query_cache(occurrence.first, out))
  {
    // cache hit
    return out;
  }

  TermVec to_visit({occurrence.first}); //TODO idk how this works
  // Note: visited is different than cache keys
  //       might want to visit without saving to the cache
  //       and if something is in the cache it wouldn't
  //       visit it again (e.g. in post-order traversal)
  UnorderedTermSet visited; //TODO should be UnorderedTermSet still now that map to pairs not terms?

  Term t;
  WalkerStepResult res;
  while(to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();

    if (in_cache(t))
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
      // visit_term requested an abort
      // return the mapping if it has been cached already
      Term out = occurrence;
      query_cache(occurrence.first, out);
      return out;
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

  // finished the traversal
  // return the cached term if available
  // otherwise just returns the original term
  query_cache(occurrence.first, out);
  return out;
}

WalkerStepResult IdentityWalker::visit_term(pair <Term, vector<int>> & occurrence)
{
  if (!preorder_)
  {
    Op op = occurrence.first->get_op();
    if (!op.is_null())
    {
      TermVec cached_children;
      Term c;
      for (auto t : term) //TODO how is a loop over the term meaningful and what should it be now?
      {
        // TODO: see if we can pass the same term as both arguments
        c = t; //TODO this needs to be a pair occurrence
        query_cache(t, c);
        cached_children.push_back(c); //TODO this needs to be only first part of pair (the term)
      }
      save_in_cache(term, solver_->make_term(op, cached_children));
    }
    else
    {
      // just keep the leaves the same
      save_in_cache(term, term); //TODO needs to be pair in second argument
    }
  }

  return Walker_Continue;
}

bool IdentityWalker::in_cache(const Term & key) const
{
  if (ext_cache_)
  {
    return ext_cache_->find(key) != ext_cache_->end();
  }
  else
  {
    return cache_.find(key) != cache_.end();
  }
}

bool IdentityWalker::query_cache(const Term & key, pair <Term, vector<int>> & out) const
{
  if (ext_cache_)
  {
    auto it = ext_cache_->find(key);
    if (it != ext_cache_->end())
    {
      out = it->second;
      return true;
    }
  }
  else
  {
    auto it = cache_.find(key);
    if (it != cache_.end())
    {
      out = it->second;
      return true;
    }
  }
  return false;
}

void IdentityWalker::save_in_cache(const Term & key, const pair <Term, vector<int>> & val)
{
  if (ext_cache_)
  {
    (*ext_cache_)[key] = val;
  }
  else
  {
    cache_[key] = val;
  }
}
}
