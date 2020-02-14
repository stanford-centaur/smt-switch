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
  smt::Term visit(smt::Term & term);
  virtual WalkerStepResult visit_term(smt::Term & term);
protected:
  smt::SmtSolver & solver_; /**< the solver to use for rebuilding terms */
  smt::UnorderedTermMap cache_; /**< cache for updating terms */
  bool clear_cache_; /**< if true, clears the cache between calls to visit */
  bool preorder_; /**< true when the current term is being visited for the first time.
                     For use in visit_term */
};

}
