/*!
 * \file numeral_utils.h
 * \brief Helpers for reading numerals and bit strings
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_NUMERAL_UTILS_H
#define SMT_SWITCH_NUMERAL_UTILS_H

#include <cstdint>
#include <string>
#include <vector>

#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"

namespace smt {

// Numerals in a base from 2 to 36, as AbsSmtSolver::make_term accepts them

/** Whether s is a non-empty string of decimal digits */
bool is_decimal_numeral(const std::string & s);

/** Whether val is a number a value of sort kind sk, INT or REAL, can be
 *  made from, with an optional leading minus: a decimal numeral, or for a
 *  REAL also a decimal or a fraction of numerals. The slash of a fraction
 *  may have spaces around it, as TermTranslator writes one.
 *  Solvers read some other strings, such as "" or "1.2.3", without an
 *  error but not as the number meant, so check before handing one over.
 *  @param sk the sort kind of the value, INT or REAL
 *  @param val the string to check
 *  @return true iff val is such a number
 */
bool is_arith_number(SortKind sk, const std::string & val);

/** The number val names in base `base`, written for is_arith_number: val
 *  itself in base 10, less a leading plus, and otherwise the same number
 *  in decimal, a REAL with a point as a fraction. In another base, val is
 *  a numeral, or for a REAL a decimal or fraction of numerals, of digits
 *  in that base (0 to 9, then a to z in either case), with an optional
 *  leading sign.
 *  @param sk the sort kind of the value, INT or REAL
 *  @param val the number in base `base`
 *  @param base from 2 to 36
 *  @return the number in base 10
 *  @throws IncorrectUsageException for another base, or a val in a base
 *  other than 10 that is not such a number
 */
std::string arith_value_to_decimal(SortKind sk,
                                   const std::string & val,
                                   std::uint64_t base);

/** The bits, most significant first, of the value of bit-vector sort `sort`
 *  that `val` names: a numeral in a base from 2 to 36 with an optional
 *  leading minus, as passed to AbsSmtSolver::make_term. A short value is
 *  zero-extended, and a negative one is written in two's complement.
 *  Throws an IncorrectUsageException for another base, a malformed
 *  numeral, a value outside the smallest signed and the largest unsigned
 *  value of the sort, or a sort that is not a bit-vector sort.
 */
std::string bv_value_to_bits(const std::string & val,
                             std::uint64_t base,
                             const Sort & sort);

namespace detail {

/** The value of c as a digit of a numeral in a base up to 36: 0 to 9,
 *  then a to z in either case
 *  @param c the character
 *  @return its value, or 36 if c is no such digit
 */
unsigned numeral_digit(char c);

/** The two's complement of the bit-vector value val, a numeral in base
 *  `base` with an optional leading sign, as AbsSmtSolver::make_term
 *  accepts it
 *  @param val the value
 *  @param base from 2 to 36
 *  @param width the width of the bit-vector
 *  @return its bits in 32-bit words, least significant first, as many as
 *  width bits take; bits of the last word above width are zero
 *  @throws IncorrectUsageException for another base, a val that is not
 *  such a numeral, or a value outside the smallest signed and the largest
 *  unsigned value of width bits
 */
std::vector<std::uint32_t> bv_value_to_words(const std::string & val,
                                             std::uint64_t base,
                                             std::uint64_t width);

/** bv_value_to_words as one number, for a width of at most 64 */
std::uint64_t bv_value_to_uint64(const std::string & val,
                                 std::uint64_t base,
                                 std::uint64_t width);

}  // namespace detail

// Helpers for implementing AbsTerm::to_int, AbsTerm::to_signed_int and
// AbsTerm::to_bits. Each throws an IncorrectUsageException if its input is
// malformed or its value does not fit in the result type.

/** Interprets a string of 0s and 1s, most significant bit first, as a
 *  bit-vector of the string's length, which may be any: unsigned, or in
 *  two's complement.
 */
std::uint64_t bits_to_uint64(const std::string & bits);
std::int64_t bits_to_int64(const std::string & bits);

namespace smtlib {

/** Parses the text of an integer value: `n`, `-n` or `(- n)`, where `n` is
 *  a decimal numeral, optionally followed by a fractional part of zeros
 *  (as in `5.0`) so that real values with an integral value are accepted.
 *  SMT-LIB numerals are never negative, and its negative integer values
 *  are `(- n)`; `-n` is an SMT-LIB symbol, but Yices2 and MathSAT print
 *  values that way outside SMT-LIB, and cvc5 and Z3 print integral reals
 *  as `n.0`.
 */
std::uint64_t int_to_uint64(const std::string & s);
std::int64_t int_to_int64(const std::string & s);

/** The bits, most significant first, of an SMT-LIB bit-vector value:
 *  `#b...`, `#x...` or `(_ bvN W)`, as many as its width.
 */
std::string bv_to_bits(const std::string & s);

/** Like bits_to_uint64 and bits_to_int64, for an SMT-LIB bit-vector value
 *  of any width: `#b...`, `#x...` or `(_ bvN W)`.
 */
std::uint64_t bv_to_uint64(const std::string & s);
std::int64_t bv_to_int64(const std::string & s);

}  // namespace smtlib

}  // namespace smt

#endif  // SMT_SWITCH_NUMERAL_UTILS_H
