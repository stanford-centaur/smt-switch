/*!
 * \file utils.h
 * \brief Utility functions
 * \author Makai Mann
 * \author Ahmed Irfan
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_UTILS_H
#define SMT_SWITCH_UTILS_H

#include <unordered_set>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"

namespace smt {

// term helper methods
void op_partition(PrimOp o, const Term & term, TermVec & out);

/** Populates a vector with conjuncts from a term
 *  @param the term to partition
 *  @param out the output vector
 *  @param include_bvand also split on BVAnd over 1-bit signals
 *         Note: this is mainly for use with Boolector which treats
 *         booleans as 1-bit bit-vectors. Using this option on a term
 *         that is known to be boolean will give you the expected
 *         partition.
 */
void conjunctive_partition(const Term & term,
                           TermVec & out,
                           bool include_bvand = false);

/** Populates a vector with disjuncts from a term
 *  @param the term to partition
 *  @param out the output vector
 *  @param include_bvor also split on BVOr over 1-bit signals
 */
void disjunctive_partition(const Term & term,
                           TermVec & out,
                           bool include_bvor = false);

void get_matching_terms(const Term & term,
                        UnorderedTermSet & out,
                        bool (*matching_fun)(const Term & term));

void get_free_symbolic_consts(const Term & term, UnorderedTermSet & out);

void get_free_symbols(const Term & term, UnorderedTermSet & out);

void get_ops(const Term & term, std::unordered_set<Op> & out);

/** Collects the subterms built with any of the given operators, including
 *  those below another one
 *  @param term the term to search
 *  @param ops the operators to look for
 *  @param out the set the subterms are added to
 */
void get_terms_with_ops(const Term & term,
                        const std::unordered_set<PrimOp> & ops,
                        UnorderedTermSet & out);

/** returns true iff l is a literal
 *  e.g. either a boolean symbolic constant or its negation
 *  NOTE will return false for nested negations, i.e. (not (not (not l)))
 *  @param l the term to check
 *  @param boolsort a boolean sort from the corresponding solver
 *         this way sort aliasing solvers are still supported
 *  @return true iff l is a literal
 */
bool is_lit(const Term & l, const Sort & boolsort);

/** Whether a term is a theory atom: a Boolean application other than a
 *  connective, a quantifier, an extract, or an equality or distinct over
 *  Booleans. Symbols and values are not theory atoms.
 *  @param t the term to check
 *  @param boolsort the Boolean sort of t's solver, so that solvers that
 *         alias Booleans and bit-vectors of width one are supported
 *  @return true iff t is a theory atom
 */
bool is_theory_atom(const Term & t, const Sort & boolsort);

}  // namespace smt

#endif  // SMT_SWITCH_UTILS_H
