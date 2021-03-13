#pragma once

#include <utility>

#include "exceptions.h"
#include "smt.h"


namespace smt
{
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
 * To implement your own walker, inherit this class and implement the
 * visit_term method. See substitution_walker.[h/cpp] for an example
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

 /** Visit a term and all its subterms in a post-order traversal //TODO STILL POSTORDER?
  *  @param term the term to visit
  *  @return the occurrence of the term after visiting, given by the pair giving the term & the term's path (returns the value of cache[term]
  *     -- if it has been cached and returns term otherwise)
  */
 std::pair<smt::Term, std::vector<int>> visit(smt::Term & node);
 using TermPairVec = std::vector<std::pair<Term, int>>;
 //using UnorderedTermPairMap = std::unordered_map<Term, std::pair<Term, std::vector<int>>>; //TODO where thsi should be...

protected:
 /** Visit a single term.
  *  Implement this method in a derived class to change the behavior
  *  of the walker
  *  By default, builds up cache from term to term's frist observed
  *   occurrence the the formula, where an occurrence is represented
  *   by a pair giving the topmost node (formula in which term appears)
  *   & the path giving position in the formula of the first occurrence
  *   of the term.
  *  The path is represented as a vector of ints that serce as coordinates
  *   for a given occurrence. For example, an empty vector indicates the
  *   topmost node and the vector [0,1] indicates the node that is the 1st
  *  child of the 0th child of the topmost node going down.
  *  @param formula the term taken to visit in visit, the topmost node of the visited formula
  *  @param term the term to visit in visit_term
  *  @param path the path for term, which we are visiting
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
  *  @param out this term is set to the cache result if there's a hit
  *  @return true iff there is a cache hit
  */
 bool query_cache(const Term & key, std::pair <Term, std::vector<int>> & out) const;

 /** Populate the cache. Automatically uses ext_cache_ if non-null.
  *  It will overwrite the existing mapping if the key is already in the cache
  *  @param key the key term
  *  @param val the value term
  */
 void save_in_cache(const Term & key, const std::pair <Term, std::vector<int>> & val);

 const smt::SmtSolver & solver_; /**< the solver to use for rebuilding terms */
 bool clear_cache_; /**< if true, clears the cache between calls to visit */
// bool preorder_; /**< true when the current term is being visited for the first
 //                   time. For use in visit_term */

private:
 // derived classes should interact with cache through the methods above only
 smt::UnorderedTermPairMap cache_;       /**< cache for updating terms */
 smt::UnorderedTermPairMap * ext_cache_; /**< external (user-provided) cache. If
                                        non-null, used instead of cache_ */
};

}
