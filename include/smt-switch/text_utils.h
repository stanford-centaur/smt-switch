/*!
 * \file text_utils.h
 * \brief Helpers for writing and reading SMT-LIB text
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_TEXT_UTILS_H
#define SMT_SWITCH_TEXT_UTILS_H

#include <functional>
#include <iosfwd>
#include <string>
#include <string_view>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"

namespace smt {

namespace smtlib {

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
inline constexpr std::string_view CHECK_SAT_ASSUMING_MODEL_STR =
    "check-sat-assuming-model";
inline constexpr std::string_view GET_UNSAT_MODEL_INTERPOLANT_STR =
    "get-unsat-model-interpolant";
inline constexpr std::string_view PUSH_STR = "push";
inline constexpr std::string_view POP_STR = "pop";
inline constexpr std::string_view RESET_ASSERTIONS_STR = "reset-assertions";
inline constexpr std::string_view RESET_STR = "reset";

/* string constants for the SMT-LIB attributes */
inline constexpr std::string_view INTERPOLATION_GROUP_STR =
    "interpolation-group";
inline constexpr std::string_view NAMED_STR = "named";

// Quoting symbols and writing terms, declarations and benchmarks in SMT-LIB

/** A symbol as SMT-LIB writes it: as is if it is a simple symbol, as the
 *  SMT-LIB standard defines one, and in bars otherwise
 *  @param s the symbol
 *  @return s, or s in bars
 */
std::string quote_symbol(const std::string & s);

/** The symbol an SMT-LIB symbol names: without its bars if it is quoted, so
 *  |a b| names a b, and as is otherwise
 *  @param s the symbol as SMT-LIB writes it
 *  @return s without its bars
 */
std::string unquote_symbol(const std::string & s);

/** An operator applied to its children as SMT-LIB writes it, (op c1 ... cn),
 *  with each child written by term_text and a bound variable's sort by
 *  sort_text, or by its to_string where either is empty. SMT-LIB writes
 *  some applications in forms of their own:
 *  - an applied function, constructor, selector or tester has no operator:
 *    the one applied, which is the first child, stands in its place, and a
 *    nullary constructor applied is that constructor alone;
 *  - a quantifier lists its bound variable with its sort,
 *    (forall ((x S)) body);
 *  - a power to a constant exponent n of 2 or more is the product of n
 *    factors with *, which solvers without SMT-LIB's ** read too, and a
 *    bit-vector power is one with bvmul.
 *  @param op the operator
 *  @param children what it is applied to
 *  @param term_text how a child is written
 *  @param sort_text how a bound variable's sort is written
 *  @return the SMT-LIB text of the application
 */
std::string application(
    const Op & op,
    const TermVec & children,
    const std::function<std::string(const Term &)> & term_text = {},
    const std::function<std::string(const Sort &)> & sort_text = {});

/** The text of a constant array, ((as const S) v). SMT-LIB's theory of
 *  arrays declares no const, so this is a solver extension, written as
 *  SMT-LIB writes a symbol whose result sort its arguments do not fix.
 *  @param sort the text of the array sort
 *  @param value the text of the value at every index
 *  @return the text of the constant array
 */
std::string const_array(const std::string & sort, const std::string & value);

/** The SMT-LIB text of an integer or real value. Its numbers lose leading
 *  zeros and gain a zero on an empty side of a decimal point, as SMT-LIB
 *  writes them: .1 becomes 0.1.
 *  @param sk the sort kind of the value, INT or REAL
 *  @param value a numeral, decimal or fraction of numerals without spaces,
 *         optionally after a sign, as in 5, +5, -0.5 or -1/2
 *  @return the SMT-LIB text of the value
 */
std::string arith_value(SortKind sk, const std::string & value);

/** The SMT-LIB declaration of a symbol, (declare-fun f (D1 ... Dn) R) for
 *  a function and (declare-fun x () S) otherwise
 *  @param symbol the symbol
 *  @param sort_text how a sort is written; by its to_string if empty
 *  @return the text of its declaration
 */
std::string declare_fun(
    const Term & symbol,
    const std::function<std::string(const Sort &)> & sort_text = {});

/** One SMT-LIB declaration of datatypes, which may refer to each other,
 *  (declare-datatypes ((D1 0) ... (Dn 0)) (cs1 ... csn))
 *  @param datatypes the datatype sorts, in the order to declare them
 *  @param sort_text how a selector's sort is written; by its to_string if
 *         empty
 *  @return the text of their declaration
 *  @throws IncorrectUsageException if datatypes is empty or holds a sort
 *          that is not a datatype
 */
std::string declare_datatypes(
    const SortVec & datatypes,
    const std::function<std::string(const Sort &)> & sort_text = {});

/** Writes assertions as an SMT-LIB benchmark: set-logic, a declaration
 *  for every uninterpreted sort, datatype and symbol they use, each kind
 *  in name order, the assertions, and check-sat. Terms and sorts are
 *  written by their to_string, so their solver must print them in
 *  SMT-LIB.
 *  @param out where to write
 *  @param logic the logic, such as ALL for a solver's default, since
 *         SMT-LIB declares nothing before set-logic
 *  @param assertions the formulas to assert
 */
void benchmark(std::ostream & out,
               const std::string & logic,
               const TermVec & assertions);

/** Whether name is a logic as SMT-LIB names them: ALL, or optional QF_ and
 *  HO_ prefixes followed by arrays (A or AX), UF, BV, FP, DT, S and an
 *  arithmetic part (IDL, RDL, LIA, LRA, LIRA, NIA, NRA, NIRA or EIA), each
 *  optional and in that order, but at least one
 *  @param name the name to check
 *  @return true iff name is such a logic
 */
bool is_logic(const std::string & name);

}  // namespace smtlib

}  // namespace smt

#endif  // SMT_SWITCH_TEXT_UTILS_H
