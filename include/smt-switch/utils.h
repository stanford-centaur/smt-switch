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

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_set>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"

namespace smt {

namespace detail {

/** Throws the IncorrectUsageException that backend_pointer_cast raises for
 *  a handle made by another solver
 *  @param h the foreign handle, named in the message
 */
[[noreturn]] void throw_foreign_handle(const Term & h);
[[noreturn]] void throw_foreign_handle(const Sort & h);
[[noreturn]] void throw_foreign_handle(const DatatypeDecl & h);
[[noreturn]] void throw_foreign_handle(const DatatypeConstructorDecl & h);
[[noreturn]] void throw_foreign_handle(const Datatype & h);

/** Mixes a part's hash into one being built up, as Boost's hash_combine
 *  does: 0x9e3779b9 is 2^32 / golden ratio, whose irregular bits spread
 *  the value, and the shifts mix in the hash so far, so the order of the
 *  parts matters and equal parts don't cancel out
 *  @param h the hash so far, updated in place
 *  @param v the next part, hashed with std::hash
 */
template <class T>
void hash_combine(std::size_t & h, const T & v)
{
  h ^= std::hash<T>{}(v) + 0x9e3779b9 + (h << 6) + (h >> 2);
}

}  // namespace detail

/** Casts a handle to the class the solver made it as
 *  @param h the handle a caller passed to the solver
 *  @return h as a T, or null for a null handle
 *  @throws IncorrectUsageException if h was made by another solver, or by a
 *          wrapper around this one
 */
template <class T, class Base>
std::shared_ptr<T> backend_pointer_cast(const std::shared_ptr<Base> & h)
{
  std::shared_ptr<T> cast = std::dynamic_pointer_cast<T>(h);
  if (h && !cast)
  {
    detail::throw_foreign_handle(h);
  }
  return cast;
}

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

/** Collects the theory atoms of a Boolean formula, as is_theory_atom
 *  defines them, without looking inside an atom
 *  @param solver the solver the formula belongs to
 *  @param formula the formula to search
 *  @param out the set the atoms are added to
 *  @param split_ites if true, an atom with if-then-else arguments is
 *         replaced by the atoms obtained by putting each branch in place
 *         of each if-then-else, and the if-then-else conditions are
 *         searched too; e.g. (= y (ite c a b)) gives (= y a), (= y b) and
 *         the atoms of c
 */
void get_theory_atoms(const SmtSolver & solver,
                      const Term & formula,
                      UnorderedTermSet & out,
                      bool split_ites = false);

/** Collects symbolic constants whose values in the solver's model alone
 *  fix the value of a term. Below a subterm whose value one child decides,
 *  only that child counts: the condition and the taken branch of an
 *  if-then-else, a false child of a conjunction, a true child of a
 *  disjunction, a false premise or true conclusion of an implication, an
 *  all-zero child of a bit-vector and, nand or multiplication, and an
 *  all-one child of a bit-vector or or nor.
 *  @param solver the solver the term belongs to, whose last check was sat
 *  @param term the term whose value to justify
 *  @param out the set the symbolic constants are added to
 */
void get_justifying_symbols(const SmtSolver & solver,
                            const Term & term,
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

/** A term as another sort, between Bool and bit-vectors or between Int and
 *  Real. A bit-vector is true when it equals 1; a value cast between Bool
 *  and a bit-vector must have width one.
 *  @param solver the solver the term and the sort belong to
 *  @param term the term to cast
 *  @param sort the sort to cast it to
 *  @return term itself if it has that sort already, else a term of sort
 *  @throws NotImplementedException for any other pair of sorts
 */
Term cast_term(const SmtSolver & solver, const Term & term, const Sort & sort);

/** An operator applied to terms, cast where the operator does not accept
 *  them as they are: the terms are cast as cast_term does, or the operator
 *  is swapped for its Boolean or bit-vector counterpart, such as And for
 *  BVAnd
 *  @param solver the solver the terms belong to
 *  @param op the operator
 *  @param terms the terms to apply it to
 *  @return a well-sorted application of op or its counterpart
 *  @throws NotImplementedException if no such cast makes it well sorted
 *  @throws IncorrectUsageException for a function applied to the wrong
 *          number of arguments
 */
Term cast_op(const SmtSolver & solver, const Op & op, const TermVec & terms);

/** The start of every name internal_name makes. A solver that makes such
 *  names refuses a user name with this start, so the two never meet.
 */
inline constexpr std::string_view INTERNAL_NAME_PREFIX = "smt_switch_internal_";

/** A name smt-switch makes up for its own use, such as
 *  `smt_switch_internal_assump_3`
 *  @param kind what the name is for, which keeps names of different kinds
 *  apart
 *  @param index which name of that kind it is
 *  @return INTERNAL_NAME_PREFIX, then `kind`, an underscore and `index`
 */
std::string internal_name(const std::string & kind, std::uint64_t index);

/** Whether a name starts with INTERNAL_NAME_PREFIX
 *  @param name the name to check
 *  @return true if internal_name could have made it
 */
bool is_internal_name(std::string_view name);

}  // namespace smt

#endif  // SMT_SWITCH_UTILS_H
