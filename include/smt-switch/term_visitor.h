/*!
 * \file term_visitor.h
 * \brief Read-only term visitor class that can be inherited to inspect
 *        terms
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Unlike IdentityWalker, it needs no solver and builds no terms, so it
 * suits collecting things from a term.
 */
#ifndef SMT_SWITCH_TERM_VISITOR_H
#define SMT_SWITCH_TERM_VISITOR_H

#include "smt-switch/smt_defs.h"
#include "smt-switch/term.h"

namespace smt {

/** What a TermVisitor does after visiting a term */
enum class VisitResult
{
  /** Visit its children */
  Continue,
  /** Leave its children out */
  Skip,
  /** Stop this call to visit */
  Abort
};

/** \class
 * TermVisitor class.
 * To implement your own visitor, inherit this class and implement the
 * visit_term method.
 */
class TermVisitor
{
 public:
  virtual ~TermVisitor() = default;

  /** Visit a term and the subterms below it in pre-order, each once. A
   *  subterm this visitor visited before, in this call or an earlier one,
   *  is not visited again.
   *  @param term the term to visit
   */
  void visit(const Term & term);

 protected:
  /** Visit a single term
   *  @param term the term to visit
   *  @return what to do next
   */
  virtual VisitResult visit_term(const Term & term) = 0;

 private:
  UnorderedTermSet visited_;
};

}  // namespace smt

#endif  // SMT_SWITCH_TERM_VISITOR_H
