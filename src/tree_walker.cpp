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
  int child_no;  //iterates over children, for tracking which child on & path
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

  visit_term(node, tree_path); //tree_path currently empty
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
  cout << "start of while loop" << endl;
  while(to_visit.size())
  {
    current_pair = to_visit.back();
    cout << "start of new round of while loop. current pair: " << current_pair.first << " , " << current_pair.second << endl;
    current_term = current_pair.first;
    child_no = current_pair.second;
    to_visit.pop_back();

    if (child_no != -1){
      //TODO add print line indicating here
      cout << "child number not flagged, tree path before add: " << vectorToString(tree_path) << endl;
      tree_path.push_back(child_no);
      cout << "tree path after push back: " << vectorToString(tree_path) << endl;
      visit_term(current_term, tree_path);
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
      cout << "should pop now, path before pop: " << vectorToString(tree_path) << endl;
      if (!tree_path.empty()){
        tree_path.pop_back();
      }
      cout << "should have popped, path afterpop: " << vectorToString(tree_path) << endl;
    }
    cout << "end of one loop, current to_visit is: " << endl;
    //for (auto const &p : to_visit) {
    //  cout << "{" << to_visit[p].first << " , " << to_visit[p].second << "}" << endl;
    //}
  }
  cout << "end of while loop" << endl;

  // finished the traversal
  // return the cached term if available
  // otherwise just returns the original term
  query_cache(node, out);
  return out;
}

TreeWalkerStepResult TreeWalker::visit_term(Term & term, vector<int> & path)
{
//  if (preorder_)
  if (true)
  {
    cout << "!preorder... visit_term " << term << " with current path: " << vectorToString(path) <<endl;
    Op op = term->get_op();
    if (!op.is_null())
    {
      TermVec cached_children;
      Term c;
      pair <Term, vector<int>> occurrence;
      for (auto t : term)
      {
       // occurrence.first = t;
        //occurrence.second = path; //TODO should update path according to which term
        //query_cache(t, occurrence); //purpose of this line? //TODO c is a term, not a pair; need to query if have something with c.first = t... amend for pairs...
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
