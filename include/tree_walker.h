#pragma once

#include <utility>

#include "exceptions.h"
#include "smt.h"

namespace smt
{
  /* vector of pairs holding terms and ints that gets used within visit in the vector to_visit
   * as a means of storing what terms we need to visit along with each term's child number relative
   * to its parent node or a "-1 flag" that indicates all of a node's children have already been visited.
  */
  using TermPairVec = std::vector<std::pair<Term, int>>;
  /* used to map from terms to their occurrences, represented as a pair of the formula it is found in and
   * the path indicating the terms placement in the formula it is find in.
   * A term's path is built up as list of indices where each index is a child number telling which path to follow
   * from the topmost node to the term's place in the formula represented as a tree.
   * For example, in the formula x+1=2, each term and its respective path is: x+1=2: []; x+1: [0]; x: [0,0]; 1: [0,1]; 2: [1]
   */
  using UnorderedTermPairMap = std::unordered_map<Term, std::pair<Term, std::vector<int>>>;

  /** \enum
   * Walker_Continue : rebuild the current term and continue
   * Walker_Skip     : skip this term and all subterms
   * Walker_Abort    : abort visiting
   */
enum TreeWalkerStepResult
{
 TreeWalker_Continue=0,
 TreeWalker_Skip,
 TreeWalker_Abort
};

/** \class
 * TreeWalker class.
 * To implement your own walker, inherit this class and override the
 * visit_term method.
 *
 * If clear_cache is set, the cache is cleared between calls to visit
 * otherwise, the cache persists
 *
 * The user can optionally pass a pointer to a cache. If that pointer
 * is non-null, it will be used in place of the internal cache.
 *
 * Important Note: The term arguments should belong to the solver provided
*/

class TreeWalker
{
public:
 TreeWalker(const smt::SmtSolver & solver,
                bool clear_cache,
                smt::UnorderedTermPairMap * ext_cache = nullptr)
     : solver_(solver), clear_cache_(clear_cache), ext_cache_(ext_cache){};

 /** Visit a term and all its subterms
  *  @param term the term to visit
  *  @return the value of cache[term]
  *    if it has been cached and returns pair of the term itself and the empty path otherwise
  */
 std::pair<smt::Term, std::vector<int>> visit(smt::Term & node);

protected:
 /** Visit a single term.
  *  Implement this method in a derived class to change the behavior
  *  of the walker.
  *  By default, builds up cache from term to term's first observed
  *   occurrence in the formula, where an occurrence is represented
  *   by a pair giving the topmost node (formula in which term appears)
  *   & the path giving position in the formula of the first occurrence
  *   of the term.
  *  The path is represented as a vector of ints that serve as coordinates
  *   for a given occurrence by giving a list of the child numbers to take
  *   from the topmost node in the tree representation of the formula down
  *   to the given occurrence in the formula. For example, an empty vector
  *   indicates the topmost node and the vector [0,1] indicates the node
  *   that is the 1st child of the 0th child of the topmost node going down.
  *   Concretely, for the formula x+1=2, each term and its respective path is:
  *     x+1=2: []
  *     x+1: [0]
  *     x: [0,0]
  *     1: [0,1]
  *     2: [1]
  *  @param formula the term taken to visit in visit, the topmost node of the visited formula
  *  @param term the term to visit in visit_term, a particular sub-term of the formula (some node in the tree representation of the full formula being traversed in visit)
  *  @param path the path for the particular term in formula, which we are visiting
  *  @return a WalkerStepResult to tell the visit method how to proceed
  */
 virtual TreeWalkerStepResult visit_term(smt::Term & formula, smt::Term & term, std::vector<int> & path);

 /** Check if key is in cache
  *  @param key
  *  @return true iff the key is in the cache
  */
 bool in_cache(const Term & key) const;

 /** Query the cache. Automatically uses ext_cache_ if non-null.
  *  @param key the term to check in the cache
  *  @param out this is set to the cache result if there's a hit
  *  @return true iff there is a cache hit
  */
 bool query_cache(const Term & key, std::pair <Term, std::vector<int>> & out) const;

 /** Populate the cache. Automatically uses ext_cache_ if non-null.
  *  It will overwrite the existing mapping if the key is already in the cache
  *  @param key the key term
  *  @param val the value pair
  */
 void save_in_cache(const Term & key, const std::pair <Term, std::vector<int>> & val);

 const smt::SmtSolver & solver_; /**< the solver to use for rebuilding terms */
 bool clear_cache_; /**< if true, clears the cache between calls to visit */

private:
 // derived classes should interact with cache through the methods above only
 smt::UnorderedTermPairMap cache_;       /**< cache for updating terms */
 smt::UnorderedTermPairMap * ext_cache_; /**< external (user-provided) cache. If
                                        non-null, used instead of cache_ */
};

}
