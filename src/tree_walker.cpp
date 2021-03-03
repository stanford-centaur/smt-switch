#include "tree_walker.h"
#include <iostream>

#include <string> //feel free to delete later

using namespace smt;
using namespace std;

namespace smt
{

//DELETE
std::string vectorToString(vector<int> v){
  std::string s;
  for (int i:v){
    s += std::to_string(i);
    s += ", ";
  }
  return s;
}

pair<Term, vector<int>> TreeWalker::visit(Term & node)
{
  cout << "starting visit()" << endl;
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

  pair <Term, vector<int>> out;
  out.first = node;
  out.second = tree_path;
  if (query_cache(node, out))
  {
    // cache hit
    return out;
  }

  TermVec to_visit({node});
  // Note: visited is different than cache keys
  //       might want to visit without saving to the cache
  //       and if something is in the cache it wouldn't
  //       visit it again (e.g. in post-order traversal)
  UnorderedTermSet visited; //TODO should be UnorderedTermSet still now that map to pairs not terms?
  //TODO add UnorderedPairSet

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
      tree_path.pop_back(); //pop last coordinate in path as move up a layer in tree
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
      pair <Term, vector<int>> out;
      out.first = node;
      out.second = tree_path; //TODO why need redo this?
      query_cache(node, out);
      return out;
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
  query_cache(node, out);
  return out;
}

TreeWalkerStepResult TreeWalker::visit_term(Term & term, vector<int> & path)
{
  if (!preorder_)
  cout << "!preorder... visit_term " << term << " with current path: " << vectorToString(path) <<endl;
  {
    Op op = term->get_op();
    if (!op.is_null())
    {
      TermVec cached_children;
      Term c;
      pair <Term, vector<int>> occurrence;
      int child_nu = 0;
      for (auto t : term)
      {
        //path.pop_back();
        //path.push_back(child_nu);
        //child_nu++;
        occurrence.first = t;
        occurrence.second = path; //TODO should update path according to which term
        query_cache(t, occurrence); //purpose of this line? //TODO c is a term, not a pair; need to query if have something with c.first = t... amend for pairs...
        cached_children.push_back(t); //TODO this needs to be only first part of pair (the term)
      }
      pair <Term, vector<int>> occ;
      occ.first = solver_->make_term(op, cached_children); //TODO should be node of visit...
      occ.second = path;
      save_in_cache(term, occ);
    }
    else
    {
      // just keep the leaves the same
      cout << "preorder... visit_term " << term << " with current path: " << vectorToString(path) <<endl;
      pair <Term, vector<int>> occ;
      occ.first = term; //TODO should be node of visit...
      occ.second = path;
      save_in_cache(term, occ);
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
