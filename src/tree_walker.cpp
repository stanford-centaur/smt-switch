#include "tree_walker.h"
#include <iostream>

#include <string>

using namespace smt;
using namespace std;

namespace smt
{

pair<Term, vector<int>> TreeWalker::visit(Term & node)
{
  // iterates over children, for tracking which child of it's parent node
  int child_no;
  // path for parts of the formula
  vector<int> tree_path;

  if (clear_cache_)
  {
    cache_.clear();

    if (ext_cache_)
    {
      ext_cache_->clear();
    }
  }

  // out is meant to store the result of querying the query cache
  // by default, out gives topmost node's occurence with which to query cache before continuing
  pair <Term, vector<int>> out;
  out.first = node;
  out.second = tree_path;
  if (query_cache(node, out))
  {
    // cache hit
    return out;
  }

  // visit top node (tree_path currently empty)
  visit_term(node, node, tree_path);
  /* to_visit is used to store terms left to visit & is a vector of pairs, where
   * the first element is the term we are saving to visit later &
   * the second element is an int serving as either an index for child's number (giving last index in a node's path) or as a marker for when all the children of the node have been visited:
   *  If the int is >=0, it indicates the number for which child the term is and
   *  If the int is -1, it serves as a flag that all children of the node have been visited and to go up a level
  * We first push back the pair (topmost node, -1) to to_visit, because when we get back to it and pop it off, we know all the children of the
  * topmost node have been visited and the full formula has been traversed.
  * Before entering the loop, we also push back all the topmost node's children, so that they and all their children can be processed before
  * getting back to the topmost node marked with a -1, indicating the traversal is finished.
  * */
  TermPairVec to_visit;
  pair<Term, int> p1 (node, -1);
  // push_back topmost node flagged with a -1
  to_visit.push_back(p1);
  // initialize child_no before starting the loop
  child_no = 0;
  // push_back all of topmost node's children to prepare for the loop
  for (auto ttt : node){
    p1.first = ttt;
    p1.second = child_no;
    to_visit.push_back(p1);
    child_no++;
  }

  // current_pair the term and int/flag we are looking at in the current iteration, last entry in to_visit
  pair<Term, int> current_pair;
  // current_term the term we are visiting in the current iteration, first element of the pair popped off of to_visit
  Term current_term;
  // pairs of term and child number or "-1 flag" that get pushed back to to_visit to visit in subsequent iterations
  pair<Term, int> pn;
  while(to_visit.size())
  {
    // get last pair on to_visit, which we visit in this iteration
    current_pair = to_visit.back();
    current_term = current_pair.first;
    child_no = current_pair.second;
    // pop off current pair, as we visit it in this iteration
    to_visit.pop_back();

    if (child_no != -1){
      // child_no != -1, so neither it nor its children have been visited
      // child number for a term gives the last index in treepath, which is a list of child numbers creating a numbered path for an occurrence
      tree_path.push_back(child_no);
      // visit current_term
      visit_term(node, current_term, tree_path);
      // push back new pair with the flag -1 to indicate that it has already been visited
      pn.first = current_term;
      pn.second = -1;
      to_visit.push_back(pn);
      // push back all children of current_term along with their respective child numbers onto to_visit to visit in subsequent iterations
      child_no = 0;
      // push back all children of current_term we will need to visit before popping all the way back to the current, parent term with the -1 flag
      for (auto tt : current_term){
        pn.first = tt;
        pn.second = child_no;
        to_visit.push_back(pn);
        child_no++;
      }
    }
    else {
      // child_no = -1, so this term and all the terms below it in the formula have been visited
      // pop off last index on tree_path to reflect that we are moving up a level in the formula now that all nodes below this have already been traversed
      if (!tree_path.empty()){
        tree_path.pop_back();
      }
    }
  }

  // finished the traversal
  // return the cached pair if available
  // otherwise just returns the pair of the original term with its empty path
  query_cache(node, out);
  return out;
}

TreeWalkerStepResult TreeWalker::visit_term(Term & formula, Term & term, vector<int> & path)
{
  // default implementation of visit_term builds up cache to map from a term in the formula to a pair giving the full formula in which it occurs and the path indicating its place in the formula

  // occurrence of the term represented by the formula in which it is found and the path indicating its placement in the formula
  pair <Term, vector<int>> occ;
  occ.first = formula;
  occ.second = path;
  // save mapping from term we're visiting to the pair containing the formula it occurs in and its path indicating its place in the formula
  save_in_cache(term, occ);

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
