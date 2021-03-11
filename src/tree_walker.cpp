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
  //iterates over children, for tracking which child on & path
  int child_no;
  //path for parts of the formula
  vector<int> tree_path;

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

  //tree_path currently empty, process top node
  visit_term(node, node, tree_path);
  TermPairVec to_visit;
  pair<Term, int> p1 (node, -1);
  to_visit.push_back(p1);
  child_no = 0;
  for (auto ttt : node){
    p1.first = ttt;
    p1.second = child_no;
    to_visit.push_back(p1);
    child_no++;
  }

  Term t;
  TreeWalkerStepResult res;
  pair<Term, int> current_pair;
  Term current_term;
  pair<Term, int> pn;
  while(to_visit.size())
  {
    current_pair = to_visit.back();
    current_term = current_pair.first;
    child_no = current_pair.second;
    to_visit.pop_back();

    if (child_no != -1){
      tree_path.push_back(child_no);
      visit_term(node, current_term, tree_path);
      pn.first = current_term;
      pn.second = -1;
      to_visit.push_back(pn);
      child_no = 0;
      for (auto tt : current_term){
        pn.first = tt;
        pn.second = child_no;
        to_visit.push_back(pn);
        child_no++;
      }
    }
    else {
      if (!tree_path.empty()){
        tree_path.pop_back();
      }
    }
  }

  // finished the traversal
  // return the cached term if available
  // otherwise just returns the original term
  query_cache(node, out);
  return out;
}

TreeWalkerStepResult TreeWalker::visit_term(Term & formula, Term & term, vector<int> & path)
{
  Op op = term->get_op();
  if (!op.is_null())
  {
    TermVec cached_children;
    Term c;
    pair <Term, vector<int>> occurrence;
    for (auto t : term)
    {
      //should we still query_cache here?
      cached_children.push_back(t);
    }
    pair <Term, vector<int>> occ;
    Term occ_key;
    occ.first = formula;
    occ_key = solver_->make_term(op, cached_children);
    occ.second = path;
    save_in_cache(occ_key, occ);
  }
  else
  {
      // just keep the leaves the same
    pair <Term, vector<int>> occ;
    occ.first = formula;
    occ.second = path;
    save_in_cache(term, occ);
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
