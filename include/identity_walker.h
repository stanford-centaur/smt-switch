#ifndef SMT_IDENTITY_WALKER_H
#define SMT_IDENTITY_WALKER_H

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
 * visit_term method.
 *
 * If clear_cache is set, the cache is cleared between calls to visit
 * otherwise, the cache persists
 *
 * Important Note: The term arguments should belong to the solver provided
 * to the identity walker, otherwise the behavior is undefined.
 */
class IdentityWalker
{
public:
  IdentityWalker(smt::SmtSolver & solver, bool clear_cache)
    : solver_(solver), clear_cache_(clear_cache) {};

  /** Visit a term and all its subterms in a pre- and post-order traversal
   *  @param term the term to visit
   *  @return the term after visiting (returns the value of cache[term]
   *     -- if it has been cached and returns term otherwise)
   */
  smt::Term visit(smt::Term & term);

protected:
  /** Visit a single term.
   *  Implement this method in a derived class to change the behavior
   *  of the walker
   *  @param term the term to visit
   *  @return a WalkerStepResult to tell the visit method how to proceed
  */
  virtual WalkerStepResult visit_term(smt::Term & term);

  smt::SmtSolver & solver_; /**< the solver to use for rebuilding terms */
  smt::UnorderedTermMap cache_; /**< cache for updating terms */
  bool clear_cache_; /**< if true, clears the cache between calls to visit */
  bool preorder_; /**< true when the current term is being visited for the first time.
                     For use in visit_term */
};

}

#endif // SMT_IDENTITY_WALKER_H
