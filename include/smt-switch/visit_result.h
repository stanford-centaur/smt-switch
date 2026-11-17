/*!
 * \file visit_result.h
 * \brief What visiting one term tells the rest of a walk
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_VISIT_RESULT_H
#define SMT_SWITCH_VISIT_RESULT_H

namespace smt {

/** What IdentityWalker, TreeWalker or TermVisitor does after visiting a term
 */
enum class VisitResult
{
  /** Visit its children */
  Continue,
  /** Leave its children out */
  Skip,
  /** Stop this call to visit */
  Abort
};

}  // namespace smt

#endif  // SMT_SWITCH_VISIT_RESULT_H
