/*********************                                                        */
/*! \file identity_walker.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Identity walker class that can be inherited and modified for
**        term traversal and manipulation.
**
**/

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
 * visit_term method.
 *
 * If clear_cache is set, the cache is cleared between calls to visit
 * otherwise, the cache persists
 *
 * The user can optionally pass a pointer to a cache. If that pointer
 * is non-null, it will be used in place of the internal cache.
 *
 * Important Note: The term arguments should belong to the solver provided
 * to the identity walker, otherwise the behavior is undefined.
 */
class IdentityWalker
{
public:
 IdentityWalker(smt::SmtSolver & solver,
                bool clear_cache,
                smt::UnorderedTermMap * ext_cache = nullptr)
     : solver_(solver), clear_cache_(clear_cache), ext_cache_(ext_cache){};

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
 bool query_cache(const Term & key, Term & out) const;

 /** Populate the cache. Automatically uses ext_cache_ if non-null.
  *  It will overwrite the existing mapping if the key is already in the cache
  *  @param key the key term
  *  @param val the value term
  */
 void save_in_cache(const Term & key, const Term & val);

 smt::SmtSolver & solver_; /**< the solver to use for rebuilding terms */
 bool clear_cache_; /**< if true, clears the cache between calls to visit */
 bool preorder_; /**< true when the current term is being visited for the first
                    time. For use in visit_term */

private:
 // derived classes should interact with cache through the methods above only
 smt::UnorderedTermMap cache_;       /**< cache for updating terms */
 smt::UnorderedTermMap * ext_cache_; /**< external (user-provided) cache. If
                                        non-null, used instead of cache_ */
};

}

