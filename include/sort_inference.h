/*********************                                                        */
/*! \file sort_inference.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Utility functions for checking sortedness and computing the
**        expected sort when building a term.
**
**/

#pragma once

#include "assert.h"

#include "ops.h"
#include "solver.h"
#include "sort.h"
#include "term.h"

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
 */
Sort compute_sort(Op op, const AbsSmtSolver * solver, const TermVec & terms);

/** Compute the expected sort of applying an operator to terms of these sorts
 *  @param op the operator
 *  @param solver the solver to use to make the new sort
 *         assumed that the passed sorts belong to this solver
 *  @param sorts a vector of sorts corresponding to the op arguments
 *  @return the expected sort
 */
Sort compute_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

// needed to use raw pointer so we could pass it from within
// const functions in an AbsSmtSolver derived class
// but also convenient to have regular SmtSolver support
Sort compute_sort(Op op, const SmtSolver solver, const TermVec & terms);
Sort compute_sort(Op op, const SmtSolver solver, const SortVec & sorts);

/* useful helper functions for sort checking */

/** Checks that terms match expected form for quantifiers
 *  To make term traversal easier considering the different
 *  handlings of quantifiers in the API's of underlying
 *  smt-switch requires that quantified terms take the form:
 *  <Forall/Exists> bound_param . body
 *  thus it takes two arguments, the parameter and a formula
 *  containing that parameter
 *  this does not limit expressivity because you can nest them
 *  @param terms the vector of terms
 *  @return true iff the terms match the expected pattern
 *  Note: this is applied directly in check_sortedness because it must
 *  be over terms
 */
bool check_quantifier_terms(const TermVec & terms);

/** Checks that sorts are expected for a quantified term
 *  e.g. that the second argument is of sort Bool
 *  similar to check_quantifier_terms but doesn't check that
 *  first argument is a parameter
 *  @param sorts the vector of sorts
 *  @return true iff the terms match the expected pattern
 *  Note: this is applied directly in compute_sort because it must
 *  be over terms
 */
 bool check_quantifier_sorts(const SortVec & sorts);

/** Checks that the sorts are equivalent
 *  @param sorts a non-empty vector of sorts
 *  @return true iff they're all equal
 */
bool equal_sorts(const SortVec & sorts);

/** Checks that the sorts have the same SortKind
 *  @param sorts a non-empty vector of sorts
 *  @return true iff they're all equal
 */
bool equal_sortkinds(const SortVec & sorts);

/** Checks that Ite arguments are well-sorted
 *  @param sorts a vector of sorts
 *  @return true iff only the sorts are valid for an ite
 */
bool check_ite_sorts(const SortVec & sorts);

/** Returns true iff all the sorts have SortKind sk
 *  @param sk the expected SortKind
 *  @param sorts the vector of Sorts to check
 *  @return true iff all SortKinds have sort sk
 */
bool check_sortkind_matches(SortKind sk, const SortVec & sorts);

/** Checks if the sorts are well-sorted for an apply operator
 *  @param sorts the vector of sorts
 *  @return true iff the first sort is a function sort
 *         and the rest of the sorts match the domain of the
 *         function
 */
bool check_apply_sorts(const SortVec & sorts);

/** Checks if the sorts are well-sorted for a select operator
 *  @param sorts the vector of sorts
 *  @param returns true iff the first sort is an array sort
 *         and the second sort is the index sort
 */
bool check_select_sorts(const SortVec & sorts);

/** Checks if the sorts are well-sorted for a store operator
 *  @param sorts the vector of sorts
 *  @param returns true iff the first sort is an array sort
 *         and the next two match the index and element sort
 */
bool check_store_sorts(const SortVec & sorts);

bool bool_sorts(const SortVec & sorts);

bool bv_sorts(const SortVec & sorts);

bool eq_bv_sorts(const SortVec & sorts);

bool real_sorts(const SortVec & sorts);

bool int_sorts(const SortVec & sorts);

bool arithmetic_sorts(const SortVec & sorts);

bool array_sorts(const SortVec & sorts);

bool function_sorts(const SortVec & sorts);

/* Helper functions for sort inference */

Sort same_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

Sort bool_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

Sort single_bit_sort(Op, const AbsSmtSolver * solver, const SortVec & sorts);

Sort real_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

Sort int_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

Sort ite_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

Sort extract_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

Sort concat_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

Sort extend_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

Sort repeat_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

Sort int_to_bv_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

Sort apply_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

Sort select_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

Sort store_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts);

}  // namespace smt
