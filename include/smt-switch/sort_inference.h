/*!
 * \file sort_inference.h
 * \brief Utility functions for checking sortedness and computing the expected
 *        sort when building a term
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_SORT_INFERENCE_H
#define SMT_SWITCH_SORT_INFERENCE_H

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"

namespace smt {

// main functions for sort checking and inference

/** Checks if applying the operator to the terms is well-sorted
 *  @param op the op to apply
 *  @param terms the vector of terms to apply it to
 *  @return true iff this is a well-sorted operation
 */
bool check_sortedness(Op op, const TermVec & terms);

/** Checks if applying the operator to the terms of these sorts is well-sorted
 *  @param op the op to apply
 *  @param sorts the vector of sorts it would be applied to
 *  @return true iff this is a well-sorted operation
 */
bool check_sortedness(Op op, const SortVec & sorts);

/** Compute the expected sort of applying an operator to these terms
 *  @param op the operator
 *  @param solver the solver to use to make the new sort
 *         assumed that the passed sorts belong to this solver
 *  @param terms the vector of terms the op would be applied to
 *  @return the expected sort
 *  @throws IncorrectUsageException if there are fewer terms than the op
 *          accepts, the indices of an extract are outside its argument, or
 *          the resulting width does not fit in 64 bits
 */
Sort compute_sort(Op op, const AbsSmtSolver * solver, const TermVec & terms);

/** Compute the expected sort of applying an operator to terms of these sorts
 *  @param op the operator
 *  @param solver the solver to use to make the new sort
 *         assumed that the passed sorts belong to this solver
 *  @param sorts a vector of sorts corresponding to the op arguments
 *  @return the expected sort
 *  @throws IncorrectUsageException if there are fewer sorts than the op
 *          accepts, the indices of an extract are outside its argument, or
 *          the resulting width does not fit in 64 bits
 */
Sort compute_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

// needed to use raw pointer so we could pass it from within
// const functions in an AbsSmtSolver derived class
// but also convenient to have regular SmtSolver support
Sort compute_sort(Op op, const SmtSolver solver, const TermVec & terms);
Sort compute_sort(Op op, const SmtSolver solver, const SortVec & sorts);

}  // namespace smt

#endif  // SMT_SWITCH_SORT_INFERENCE_H
