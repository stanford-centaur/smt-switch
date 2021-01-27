#include "tree_walker.h"

using namespace smt;
using namespace std;

namespace smt
{

Term TreeWalker::visit(pair <Term, vector<int>> & occurrence)
{
  int child_no = -1; //iterates over children, for tracking which child on & path
  vector<int> tree_path; //path ; TODO need std::..?

  if (clear_cache_)
  {
    cache_.clear();

    if (ext_cache_)
    {
      ext_cache_->clear();
    }
  }

  pair <Term, vector<int>> out = occurrence;
  if (query_cache(occurrence.first, out))
  {
    // cache hit
    return out.first;
  }

  TermVec to_visit({occurrence.first});
  // Note: visited is different than cache keys
  //       might want to visit without saving to the cache
  //       and if something is in the cache it wouldn't
  //       visit it again (e.g. in post-order traversal)
  UnorderedTermSet visited; //TODO should be UnorderedTermSet still now that map to pairs not terms?

  Term t;
  TreeWalkerStepResult res;
  while(to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();

    //TODO increment iterator for children
    ++child_no; //TODO should 0 for first loop and 1 in next etc

    if (in_cache(t))
    {
      // cache hit
      // TODO reset iterator for children
      tree_path.pop_back(); //add to path
      //child_no = -1;
      continue;
    }

    // in preorder if it has not been seen before
    preorder_ = (visited.find(t) == visited.end());
    // add to visited after determining whether we're in the pre-
    // or post-order
    visited.insert(t);
    res = visit_term(t, tree_path);

    if (res == TreeWalker_Abort)
    {
      // visit_term requested an abort
      // return the mapping if it has been cached already
      pair <Term, vector<int>> out = occurrence;
      query_cache(occurrence.first, out);
      return out.first;
    }

    if (preorder_)
    {
      if (res == TreeWalker_Continue)
      {
        to_visit.push_back(t);
        tree_path.push_back(child_no); //path back path, going down new level
        child_no = -1; //reset counter for new set of children to take
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
  return out.first;
}

TreeWalkerStepResult TreeWalker::visit_term(Term & term, vector<int> & path)
{
  if (!preorder_)
  {
    Op op = term->get_op();
    if (!op.is_null())
    {
      TermVec cached_children;
      Term c;
      pair <Term, vector<int>> occurrence;
      for (auto t : term) //TODO how is a loop over the term meaningful and what should it be now? iterates over term's children?
      {
        // TODO: see if we can pass the same term as both arguments
        //c = t; //TODO this needs to be a pair occurrence
        //TODO make pair for (term=c, path=computed somehow)
        occurrence.first = t;
        occurrence.second = path;
        query_cache(t, occurrence); //purpose of this line? //TODO c is a term, not a pair; need to query if have something with c.first = t... amend for pairs...
        cached_children.push_back(t); //TODO this needs to be only first part of pair (the term)
      }
      pair <Term, vector<int>> occ;
      occ.first = solver_->make_term(op, cached_children);
      occ.second = path;
      save_in_cache(term, occ);
    }
    else
    {
      // just keep the leaves the same
      pair <Term, vector<int>> occ;
      occ.first = term;
      occ.second = path;
      save_in_cache(term, occ); //TODO needs to be pair in second argument
    }
  }

  return TreeWalker_Continue;
}

bool TreeWalker::in_cache(const Term & key) const
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

bool TreeWalker::query_cache(const Term & key, pair <Term, vector<int>> & out) const
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

void TreeWalker::save_in_cache(const Term & key, const pair <Term, vector<int>> & val)
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
