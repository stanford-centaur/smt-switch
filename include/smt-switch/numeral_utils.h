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

namespace smt::smtlib {

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

}  // namespace smt::smtlib

namespace smt::backend {

/** The value of an option that takes a natural number
 *  @param option the option, used in the error message
 *  @param value the value given for it
 *  @return the number
 *  @throws IncorrectUsageException for a value that is not a decimal
 *  numeral below 2^64
 */
std::uint64_t parse_nat_opt(const std::string & option,
                            const std::string & value);

}  // namespace smt::backend

#endif  // SMT_SWITCH_NUMERAL_UTILS_H
