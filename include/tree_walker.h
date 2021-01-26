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
enum WalkerStepResult
{
 Walker_Continue=0,
 Walker_Skip,
 Walker_Abort
};

/** \class
 * IdentityWalker class.
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
                smt::UnorderedTermMap * ext_cache = nullptr)
     : solver_(solver), clear_cache_(clear_cache), ext_cache_(ext_cache){};

 /** Visit a term and all its subterms in a post-order traversal
  *  the member variable preorder_ is true if it's the first time seeing
  *  a subterm and false if the traversal is in post-order already
  *  @param term the term to visit
  *  @return the term after visiting (returns the value of cache[term]
  *     -- if it has been cached and returns term otherwise)
  */
 smt::Term visit(std::pair <smt::Term, std::vector<int>> & occurrence); //TODO should be Term & term or just Term?, match w visit_term

protected:
 /** Visit a single term.
  *  Implement this method in a derived class to change the behavior
  *  of the walker
  *  @param term the term to visit
  *  @return a WalkerStepResult to tell the visit method how to proceed
  */
 virtual WalkerStepResult visit_term(smt::Term & term, std::vector<int>> & path)

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
 bool query_cache(const Term & key, pair <Term, vector<int>> & out) const;

 /** Populate the cache. Automatically uses ext_cache_ if non-null.
  *  It will overwrite the existing mapping if the key is already in the cache
  *  @param key the key term
  *  @param val the value term
  */
 void save_in_cache(const Term & key, const pair <Term, vector<int>> & val); //TODO why query_cache and this dont need std:: and smt:: apparently bc const

 const smt::SmtSolver & solver_; /**< the solver to use for rebuilding terms */
 bool clear_cache_; /**< if true, clears the cache between calls to visit */
 bool preorder_; /**< true when the current term is being visited for the first
                    time. For use in visit_term */

private:
 // derived classes should interact with cache through the methods above only
 smt::UnorderedTermMap cache_;       /**< cache for updating terms */ //TODO would I have to change these too as cache map is mapping to pairs now
 smt::UnorderedTermMap * ext_cache_; /**< external (user-provided) cache. If
                                        non-null, used instead of cache_ */
};

}
