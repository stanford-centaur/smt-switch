/*********************                                                        */
/*! \file logging_sort_computation.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Functions for computing the expected sort when building a term.
**
**
**/

#include "logging_sort.h"
#include "ops.h"

namespace smt {

/** Compute expected LoggingSort
 *  @param op the operator
 *  @param sorts a vector of sorts corresponding to the op arguments
 *         these should be logging sorts
 *  @param wrapped_res_sort the underlying sort that the logging sort
 *         result should wrap
 *  @return the new logging sort
 */
Sort compute_sort(Op op, SortVec sorts, Sort wrapped_res_sort);

/* Common sort computation helper functions */

Sort same_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort);

Sort bool_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort);

Sort real_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort);

Sort int_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort);

Sort ite_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort);

Sort extract_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort);

Sort concat_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort);

Sort extend_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort);

Sort repeat_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort);

Sort int_to_bv_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort);

Sort apply_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort);

Sort select_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort);

Sort store_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort);

}  // namespace smt
