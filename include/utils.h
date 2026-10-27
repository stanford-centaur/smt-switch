/*********************                                                        */
/*! \file utils.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Ahmed Irfan
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Utility functions.
**
**
**/

#pragma once

#include <cstdint>
#include <memory>
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_map>

#include "ops.h"
#include "smt_defs.h"
#include "term.h"
#include "term_translator.h"

// macro for getting string value of another macro
// i.e. STRFY(FOO) := "FOO"
#define STRHELPER(A) #A
#define STRFY(A) STRHELPER(A)

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

void get_ops(const Term & term, UnorderedOpSet & out);

/** returns true iff l is a literal
 *  e.g. either a boolean symbolic constant or its negation
 *  NOTE will return false for nested negations, i.e. (not (not (not l)))
 *  @param l the term to check
 *  @param boolsort a boolean sort from the corresponding solver
 *         this way sort aliasing solvers are still supported
 *  @return true iff l is a literal
 */
bool is_lit(const Term & l, const Sort & boolsort);

// Returns a string in DIMACs format for a given cnf formula
void cnf_to_dimacs(Term cnf, std::ostringstream & y);

// Converts any boolean formula to cnf, formula is the formula to be converted
// to a cnf. Only the connectives not, and, or, xor, => and Boolean = are
// encoded; any other subterm, such as an ite or (bvult x y), is kept whole as
// an atom
Term to_cnf(Term formula, SmtSolver s);

// Returns true if the formula is in cnf form, else false
bool is_cnf(Term formula);

/* string constants for the SMT-LIB commands */
inline constexpr std::string_view SET_OPTION_STR = "set-option";
inline constexpr std::string_view SET_LOGIC_STR = "set-logic";
inline constexpr std::string_view DECLARE_FUN_STR = "declare-fun";
inline constexpr std::string_view DEFINE_FUN_STR = "define-fun";
inline constexpr std::string_view DECLARE_SORT_STR = "declare-sort";
inline constexpr std::string_view DEFINE_SORT_STR = "define-sort";
inline constexpr std::string_view DECLARE_DATATYPE_STR = "declare-datatypes";
inline constexpr std::string_view ASSERT_STR = "assert";
inline constexpr std::string_view CHECK_SAT_STR = "check-sat";
inline constexpr std::string_view CHECK_SAT_ASSUMING_STR = "check-sat-assuming";
inline constexpr std::string_view GET_VALUE_STR = "get-value";
inline constexpr std::string_view GET_UNSAT_ASSUMPTIONS_STR =
    "get-unsat-assumptions";
inline constexpr std::string_view GET_INTERPOLANT_STR = "get-interpolant";
inline constexpr std::string_view GET_INTERPOLANTS_STR = "get-interpolants";
inline constexpr std::string_view PUSH_STR = "push";
inline constexpr std::string_view POP_STR = "pop";
inline constexpr std::string_view RESET_ASSERTIONS_STR = "reset-assertions";
inline constexpr std::string_view RESET_STR = "reset";

/* string constants for the SMT-LIB attributes */
inline constexpr std::string_view INTERPOLATION_GROUP_STR =
    "interpolation-group";
inline constexpr std::string_view NAMED_STR = "named";

// Helpers for implementing AbsTerm::to_int and AbsTerm::to_signed_int.
// Each throws an IncorrectUsageException if its input is malformed or its
// value does not fit in the result type.

/** Parses the text of an integer value: `n`, `-n` or `(- n)`, where `n` is
 *  a decimal numeral, optionally followed by a fractional part of zeros
 *  (as in `5.0`) so that real values with an integral value are accepted.
 *  SMT-LIB numerals are never negative, and its negative integer values
 *  are `(- n)`; `-n` is an SMT-LIB symbol, but Yices2 and MathSAT print
 *  values that way outside SMT-LIB, and cvc5 and Z3 print integral reals
 *  as `n.0`.
 */
std::uint64_t smtlib_int_to_uint64(const std::string & s);
std::int64_t smtlib_int_to_int64(const std::string & s);

/** Interprets a string of 0s and 1s, most significant bit first, as a
 *  bit-vector of the string's length: unsigned, or in two's complement.
 *  Throws for bit-vectors wider than 64 bits, whatever their value.
 */
std::uint64_t bits_to_uint64(const std::string & bits);
std::int64_t bits_to_int64(const std::string & bits);

/** Like bits_to_uint64 and bits_to_int64, for an SMT-LIB bit-vector value:
 *  `#b...`, `#x...` or `(_ bvN W)`.
 */
std::uint64_t smtlib_bv_to_uint64(const std::string & s);
std::int64_t smtlib_bv_to_int64(const std::string & s);

/** The bits, most significant first, of the value of bit-vector sort `sort`
 *  that `val` names: a numeral in base 2, 10 or 16 with an optional leading
 *  minus, as passed to AbsSmtSolver::make_term. A short value is
 *  zero-extended, and a negative one is written in two's complement.
 *  Throws an IncorrectUsageException for another base, a malformed
 *  numeral, a value outside the smallest signed and the largest unsigned
 *  value of the sort, or a sort that is not a bit-vector sort.
 */
std::string bv_value_to_bits(const std::string & val,
                             std::uint64_t base,
                             const Sort & sort);

/** The start of every name internal_name makes. A solver that makes such
 *  names refuses a user name with this start, so the two never meet.
 */
const std::string INTERNAL_NAME_PREFIX = "smt_switch_internal_";

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
bool is_internal_name(const std::string & name);

// -----------------------------------------------------------------------------

/** \class
 * UnsatcoreReducer class.
 * Implements an iterative unsatcore reducer procedure.
 *
 * reducer_solver is the solver that will be used for unsatcore extraction in
 * the procedure. It is different from the ext_solver (external solver used to
 * create the formula and assump)
 *
 */
class UnsatCoreReducer
{
 public:
  explicit UnsatCoreReducer(SmtSolver reducer_solver);

  /** The main method to reduce the assump (vector of assumptions). The method
   *  assumes that the conjunction of the formula and assump is unsatisfiable.
   *  @param input formula
   *  @param input vector of assumptions
   *  @param output vector for the reduced assumptions
   *  @param output vector for the removed assumptions
   *  @param iter is the number of iterations done in the method. Default is 0,
   *         and it means that the result in out_red will be minimal.
   *  @param rand_seed if strickly positive then assump will be shuffled.
   *  returns false if the formula conjoined with the assump is satisfiable,
   *          otherwise returns true
   */
  bool reduce_assump_unsatcore(const Term & formula,
                               const TermVec & assump,
                               TermVec & out_red,
                               TermVec * out_rem = nullptr,
                               unsigned iter = 0,
                               unsigned rand_seed = 0);

  /** The additional method to reduce the assump (vector of assumptions). The
   * method assumes that the conjunction of the formula and assump is
   * unsatisfiable. This will iterate through the assump and requires at most
   * size(assump) queries. Note: this function assumes that there are no
   * duplicate assumptions from the second input vector.
   *  @param input formula
   *  @param input vector of assumptions
   *  @param output vector for the reduced assumptions
   *  @param output vector for the removed assumptions
   *  @param iter is the number of iterations done in the method. Default is 0,
   *         and it means that the result in out_red will be minimal.
   *  returns false if the formula conjoined with the assump is satisfiable,
   *          otherwise returns true
   */
  bool linear_reduce_assump_unsatcore(const Term & formula,
                                      const TermVec & assump,
                                      TermVec & out_red,
                                      TermVec * out_rem = nullptr,
                                      unsigned iter = 0);

  /** This clears the term translation cache. Note, term translator is used to
   *  translate the terms of the external solver to the
   *  unsat-assumption-reducer-solver. A use-case of this method is to call it
   * before calling the reduce_assump_unsat from one call to another call when
   * the external solver in the first call is different from the second call.
   */
  void clear_term_translation_cache();

 private:
  /** returns a label that will be used to precondition the assumption term 't'
   *  @param Input term t
   *  return a boolean label for the term t
   */
  Term label(const Term & t);

  SmtSolver reducer_;          ///< solver for unsatcore-based reduction
  TermTranslator to_reducer_;  ///< translator for converting terms from
                               ///< ext_solver to reducer_
  UnorderedTermMap labels_;    ///< labels for unsat cores
};

// -----------------------------------------------------------------------------

/** A generic implementation of Disjoint Sets for smt-switch terms.
 *  Supports a comparator for ranking of terms.
 */
class DisjointSet
{
 public:
  explicit DisjointSet(bool (*c)(const Term & a, const Term & b));

  /** Add two terms a and b in the same set.
   * @param Term a to be added in the same set
   * @param Term b to be added in the same set
   */
  void add(const Term & a, const Term & b);

  /** Find the representative (leader) of the term t.
   * @param Term t whose respresentative to be returned.
   * returns the representative term.
   */
  Term find(const Term & t) const;

  /** Clears the disjoint set
   */
  void clear();

 private:
  // Compare function for ranking
  bool (*comp)(const Term & a, const Term & b);

  // member to group's leader
  UnorderedTermMap leader_;
  // group leader to group
  std::unordered_map<Term, UnorderedTermSet> group_;
};

}  // namespace smt
