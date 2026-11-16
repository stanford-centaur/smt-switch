/*!
 * \file numeral_utils.cpp
 * \brief Helpers for reading numerals and bit strings
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Besides the smtlib:: parsers, this file defines the numeral readers of
 * AbsSmtSolver and AbsTerm, which share its helpers.
 */
#include "smt-switch/numeral_utils.h"

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <string>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {

namespace {

std::string trim_spaces(const std::string & s)
{
  const std::string::size_type begin = s.find_first_not_of(" \t\n\r");
  if (begin == std::string::npos)
  {
    return "";
  }
  const std::string::size_type end = s.find_last_not_of(" \t\n\r");
  return s.substr(begin, end - begin + 1);
}

/* std::isdigit for a char, which std::all_of cannot take directly */
bool is_decimal_digit(char c)
{
  return std::isdigit(static_cast<unsigned char>(c)) != 0;
}

/** Accumulates the decimal numeral `digits` into `value`.
 *  Returns false if it is empty, has a non-digit or overflows.
 */
bool decimal_to_uint64(const std::string & digits, std::uint64_t & value)
{
  if (digits.empty())
  {
    return false;
  }
  const std::uint64_t max = std::numeric_limits<std::uint64_t>::max();
  value = 0;
  for (char c : digits)
  {
    if (!is_decimal_digit(c))
    {
      return false;
    }
    const std::uint64_t d = static_cast<std::uint64_t>(c - '0');
    if (value > (max - d) / 10)
    {
      return false;
    }
    value = value * 10 + d;
  }
  return true;
}

/** Parses an integer value into its sign and magnitude.
 *  See smtlib::int_to_uint64 for the accepted syntax.
 */
void parse_smtlib_int(const std::string & s,
                      bool & negative,
                      std::uint64_t & magnitude)
{
  std::string text = trim_spaces(s);
  negative = false;
  if (text.size() > 2 && text.substr(0, 2) == "(-" && text.back() == ')')
  {
    negative = true;
    text = trim_spaces(text.substr(2, text.size() - 3));
  }
  else if (!text.empty() && text[0] == '-')
  {
    negative = true;
    text = text.substr(1);
  }

  const std::string::size_type point = text.find('.');
  if (point != std::string::npos)
  {
    const std::string fraction = text.substr(point + 1);
    if (fraction.empty()
        || fraction.find_first_not_of('0') != std::string::npos)
    {
      throw IncorrectUsageException(
          "Can't convert " + s + " to an integer: it is not an integer value");
    }
    text = text.substr(0, point);
  }

  if (!decimal_to_uint64(text, magnitude))
  {
    if (!text.empty()
        && text.find_first_not_of("0123456789") == std::string::npos)
    {
      throw IncorrectUsageException("Can't convert " + s
                                    + " to an integer: it does not fit in 64 "
                                      "bits");
    }
    throw IncorrectUsageException(
        "Can't convert " + s + " to an integer: it is not an integer value");
  }
}

/** Interprets the low `width` bits of `value` in two's complement. */
std::int64_t to_twos_complement(std::uint64_t value, std::uint64_t width)
{
  const std::uint64_t sign_bit = std::uint64_t(1) << (width - 1);
  if ((value & sign_bit) == 0)
  {
    return static_cast<std::int64_t>(value);
  }
  // the value is 2^width - magnitude; 2^64 wraps around to 0
  const std::uint64_t two_to_width =
      width == 64 ? 0 : (std::uint64_t(1) << width);
  const std::uint64_t magnitude = two_to_width - value;
  if (magnitude == sign_bit)
  {
    // the minimum value, whose magnitude does not fit in the result type
    return -static_cast<std::int64_t>(sign_bit - 1) - 1;
  }
  return -static_cast<std::int64_t>(magnitude);
}

void check_bit_string(const std::string & bits)
{
  if (bits.empty() || bits.find_first_not_of("01") != std::string::npos)
  {
    throw IncorrectUsageException("Can't convert " + bits
                                  + " to an integer: it is not a bit string");
  }
}

IncorrectUsageException not_a_bv_value(const std::string & s)
{
  return IncorrectUsageException("Can't convert " + s
                                 + " to bits: it is not a bit-vector value");
}

/** The unsigned value of the bit-vector `bits`, a non-empty string of 0s and
 *  1s, most significant first. Throws if a bit above the low 64 is set. `s`
 *  is the text the bits were read from.
 */
std::uint64_t low_64_bits(const std::string & bits, const std::string & s)
{
  const std::string::size_type high = bits.size() > 64 ? bits.size() - 64 : 0;
  if (bits.find('1') < high)
  {
    throw IncorrectUsageException(
        "Can't convert " + s
        + " to an unsigned integer: it does not fit in 64 bits");
  }
  std::uint64_t value = 0;
  for (std::string::size_type i = high; i < bits.size(); ++i)
  {
    value = (value << 1) | static_cast<std::uint64_t>(bits[i] - '0');
  }
  return value;
}

/** Like low_64_bits, but in two's complement. Throws unless every bit above
 *  the low 64 equals bit 63, extending its sign.
 */
std::int64_t low_64_bits_signed(const std::string & bits, const std::string & s)
{
  const std::string::size_type high = bits.size() > 64 ? bits.size() - 64 : 0;
  if (bits.find_first_not_of(bits[high]) < high)
  {
    throw IncorrectUsageException(
        "Can't convert " + s
        + " to a signed integer: it does not fit in 64 bits");
  }
  std::uint64_t value = 0;
  for (std::string::size_type i = high; i < bits.size(); ++i)
  {
    value = (value << 1) | static_cast<std::uint64_t>(bits[i] - '0');
  }
  return to_twos_complement(value, bits.size() - high);
}

/** The exception for a val that is not a base-`base` numeral */
IncorrectUsageException not_a_numeral(const std::string & val,
                                      std::uint64_t base)
{
  return IncorrectUsageException("Value " + val + " is not a base-"
                                 + std::to_string(base) + " numeral");
}

/* The value of c as a digit of a numeral in a base up to 36: 0 to 9,
 *  then a to z in either case
 *  @param c the character
 *  @return its value, or 36 if c is no such digit
 */
unsigned numeral_digit(char c)
{
  return static_cast<unsigned>(c >= '0' && c <= '9'   ? c - '0'
                               : c >= 'a' && c <= 'z' ? c - 'a' + 10
                               : c >= 'A' && c <= 'Z' ? c - 'A' + 10
                                                      : 36);
}

/** The decimal numeral of the non-empty string of base-`base` digits
 *  `digits`, 0 to 9 then a to z in either case, or "" if digits is not one
 */
std::string digits_to_decimal(const std::string & digits, unsigned base)
{
  if (digits.empty())
  {
    return "";
  }
  std::string dec = "0";
  for (char c : digits)
  {
    unsigned digit = numeral_digit(c);
    if (digit >= base)
    {
      return "";
    }
    // dec = dec * base + digit
    unsigned carry = digit;
    for (auto it = dec.rbegin(); it != dec.rend(); ++it)
    {
      unsigned current = static_cast<unsigned>(*it - '0') * base + carry;
      *it = static_cast<char>('0' + current % 10);
      carry = current / 10;
    }
    while (carry > 0)
    {
      dec.insert(dec.begin(), static_cast<char>('0' + carry % 10));
      carry /= 10;
    }
  }
  return dec;
}

/* AbsSmtSolver::bv_value_to_words, which smtlib::bv_to_bits also needs */
std::vector<std::uint32_t> value_words(const std::string & val,
                                       std::uint64_t base,
                                       std::uint64_t width)
{
  if (base < 2 || base > 36)
  {
    throw IncorrectUsageException("Only accepted bases are 2 to 36, but got "
                                  + std::to_string(base));
  }
  bool negative = val.find('-') == 0;
  std::string::size_type first = negative || val.find('+') == 0 ? 1 : 0;
  if (first == val.size())
  {
    throw not_a_numeral(val, base);
  }
  // the magnitude, least significant word first
  std::vector<std::uint32_t> words;
  // whether the magnitude grew past the words that can hold more bits than
  // width, after which it is no longer computed
  bool too_wide = false;
  // a power of two
  if ((base & (base - 1)) == 0)
  {
    // each digit is a whole number of bits, so shift them in from the last
    // digit on
    unsigned digit_bits = 0;
    while ((std::uint64_t{ 1 } << digit_bits) < base)
    {
      ++digit_bits;
    }
    // bits read but not yet a whole word, lowest first
    std::uint64_t pending = 0;
    unsigned pending_bits = 0;
    for (std::string::size_type i = val.size(); i-- > first;)
    {
      unsigned digit = numeral_digit(val[i]);
      if (digit >= base)
      {
        throw not_a_numeral(val, base);
      }
      pending |= std::uint64_t{ digit } << pending_bits;
      pending_bits += digit_bits;
      if (pending_bits >= 32)
      {
        words.push_back(static_cast<std::uint32_t>(pending));
        pending >>= 32;
        pending_bits -= 32;
      }
    }
    // the rest, which may be zero
    words.push_back(static_cast<std::uint32_t>(pending));
  }
  else
  {
    // read the digits in groups of n, with n as large as keeps base^n
    // within a word, multiplying by base^n and adding each group in turn
    std::uint64_t group_scale = base;
    std::string::size_type group = 1;
    while (group_scale * base <= 0xffffffff)
    {
      group_scale *= base;
      ++group;
    }
    // the first group takes the digits left over, so the rest are full
    std::string::size_type count = val.size() - first;
    std::string::size_type length = count % group ? count % group : group;
    for (std::string::size_type pos = first; pos < val.size();
         pos += length, length = group)
    {
      // the group as a number, and base^(its length)
      std::uint64_t value = 0;
      std::uint64_t scale = 1;
      for (std::string::size_type i = pos; i < pos + length; ++i)
      {
        unsigned digit = numeral_digit(val[i]);
        if (digit >= base)
        {
          throw not_a_numeral(val, base);
        }
        value = value * base + digit;
        scale *= base;
      }
      // the remaining digits are only checked
      if (too_wide)
      {
        continue;
      }
      // words = words * scale + value
      std::uint64_t carry = value;
      for (std::uint32_t & word : words)
      {
        std::uint64_t current = word * scale + carry;
        word = static_cast<std::uint32_t>(current);
        carry = current >> 32;
      }
      if (carry)
      {
        words.push_back(static_cast<std::uint32_t>(carry));
      }
      // the last word is not zero, so more words than these hold more bits
      // than width
      too_wide = words.size() > width / 32 + 1;
    }
  }
  // drop the zero words at the top, so the last word holds the highest one
  while (!words.empty() && words.back() == 0)
  {
    words.pop_back();
  }
  // the bits up to and including the highest one
  std::uint64_t magnitude_bits = 0;
  if (!words.empty())
  {
    magnitude_bits = 32 * (words.size() - 1);
    for (std::uint32_t top = words.back(); top; top >>= 1)
    {
      ++magnitude_bits;
    }
  }
  // a magnitude of all width bits only fits negated, as -2^(width - 1):
  // a single bit in the last word, and every word below it zero
  if (too_wide || magnitude_bits > width
      || (negative && magnitude_bits == width
          && ((words.back() & (words.back() - 1)) != 0
              || std::count(words.begin(), words.end() - 1, 0u)
                     != static_cast<std::ptrdiff_t>(words.size() - 1))))
  {
    throw IncorrectUsageException("Value " + val + " does not fit in "
                                  + std::to_string(width) + " bits");
  }
  // as many words as width bits take
  words.resize((width + 31) / 32, 0);
  if (negative)
  {
    // the two's complement inverts every bit, then adds one
    std::uint64_t carry = 1;
    for (std::uint32_t & word : words)
    {
      std::uint64_t current = std::uint64_t{ ~word } + carry;
      word = static_cast<std::uint32_t>(current);
      carry = current >> 32;
    }
  }
  // clear the bits above width, which the two's complement sets
  if (width % 32)
  {
    words.back() &= (std::uint32_t{ 1 } << (width % 32)) - 1;
  }
  return words;
}

/* Whether s is a non-empty string of decimal digits */
bool is_decimal_numeral(const std::string & s)
{
  return !s.empty() && std::all_of(s.begin(), s.end(), is_decimal_digit);
}

/* Whether val is a number a value of sort kind sk, INT or REAL, can be
 * made from, with an optional leading minus: a decimal numeral, or for a
 * REAL also a decimal or a fraction of numerals, with spaces allowed
 * around the slash
 */
bool is_arith_number(SortKind sk, const std::string & val)
{
  std::string magnitude = val.find('-') == 0 ? val.substr(1) : val;
  if (is_decimal_numeral(magnitude))
  {
    return true;
  }
  std::string::size_type separator = magnitude.find_first_of("./");
  if (sk != REAL || separator == std::string::npos)
  {
    return false;
  }
  std::string whole = magnitude.substr(0, separator);
  std::string part = magnitude.substr(separator + 1);
  if (magnitude[separator] == '/')
  {
    whole = whole.substr(0, whole.find_last_not_of(' ') + 1);
    std::string::size_type start = part.find_first_not_of(' ');
    part = start == std::string::npos ? "" : part.substr(start);
  }
  return is_decimal_numeral(whole) && is_decimal_numeral(part);
}

}  // namespace

std::uint64_t AbsTerm::bits_to_uint64(const std::string & bits)
{
  check_bit_string(bits);
  return low_64_bits(bits, bits);
}

std::int64_t AbsTerm::bits_to_int64(const std::string & bits)
{
  check_bit_string(bits);
  return low_64_bits_signed(bits, bits);
}

std::vector<std::uint32_t> AbsSmtSolver::bv_value_to_words(
    const std::string & val, std::uint64_t base, std::uint64_t width)
{
  return value_words(val, base, width);
}

std::uint64_t AbsSmtSolver::bv_value_to_uint64(const std::string & val,
                                               std::uint64_t base,
                                               std::uint64_t width)
{
  std::vector<std::uint32_t> words = bv_value_to_words(val, base, width);
  return words.size() > 1 ? std::uint64_t{ words[1] } << 32 | words[0]
                          : words[0];
}

std::uint64_t AbsSmtSolver::parse_nat_opt(const std::string & option,
                                          const std::string & value)
{
  std::uint64_t number = 0;
  if (!decimal_to_uint64(value, number))
  {
    throw IncorrectUsageException("The option " + option
                                  + " takes a natural number below 2^64, not "
                                  + value);
  }
  return number;
}

std::string AbsSmtSolver::arith_value_to_decimal(SortKind sk,
                                                 const std::string & val,
                                                 std::uint64_t base)
{
  bool negative = val.find('-') == 0;
  std::string magnitude = negative || val.find('+') == 0 ? val.substr(1) : val;
  if (base == 10)
  {
    // a second sign is left in, for the check to refuse
    std::string decimal =
        negative || magnitude.find_first_of("+-") == 0 ? val : magnitude;
    if (!is_arith_number(sk, decimal))
    {
      throw IncorrectUsageException("Value " + val + " is not a number of sort "
                                    + to_string(sk));
    }
    return decimal;
  }
  if (base < 2 || base > 36)
  {
    throw IncorrectUsageException("Only accepted bases are 2 to 36, but got "
                                  + std::to_string(base));
  }
  unsigned b = static_cast<unsigned>(base);
  std::string::size_type separator =
      sk == REAL ? magnitude.find_first_of("./") : std::string::npos;
  std::string whole = magnitude.substr(0, separator);
  std::string decimal;
  if (separator == std::string::npos)
  {
    decimal = digits_to_decimal(whole, b);
  }
  else
  {
    std::string part = magnitude.substr(separator + 1);
    std::string numerator;
    std::string denominator;
    if (magnitude[separator] == '/')
    {
      numerator = digits_to_decimal(whole, b);
      denominator = digits_to_decimal(part, b);
    }
    else if (!whole.empty() && !part.empty())
    {
      // the digits after the point count base^-1, base^-2, ..., so the
      // number is all its digits over base^(digits after the point), a 1
      // followed by that many zeros
      numerator = digits_to_decimal(whole + part, b);
      denominator = digits_to_decimal("1" + std::string(part.size(), '0'), b);
    }
    decimal = numerator.empty() || denominator.empty()
                  ? ""
                  : numerator + "/" + denominator;
  }
  if (decimal.empty())
  {
    throw IncorrectUsageException("Value " + val + " is not a base-"
                                  + std::to_string(base) + " number of sort "
                                  + to_string(sk));
  }
  return negative ? "-" + decimal : decimal;
}

std::string AbsSmtSolver::bv_value_to_bits(const std::string & val,
                                           std::uint64_t base,
                                           const Sort & sort)
{
  if (sort->get_sort_kind() != BV)
  {
    throw IncorrectUsageException("Sort " + sort->to_string()
                                  + " is not a bit-vector sort");
  }
  std::uint64_t width = sort->get_width();
  std::vector<std::uint32_t> words = bv_value_to_words(val, base, width);
  // bit i is in word i / 32, and the string starts with the highest bit
  std::string bits(width, '0');
  for (std::uint64_t i = 0; i < width; ++i)
  {
    if ((words[i / 32] >> (i % 32)) & 1)
    {
      bits[width - 1 - i] = '1';
    }
  }
  return bits;
}

namespace smtlib {

std::uint64_t int_to_uint64(const std::string & s)
{
  bool negative;
  std::uint64_t magnitude;
  parse_smtlib_int(s, negative, magnitude);
  if (negative && magnitude != 0)
  {
    throw IncorrectUsageException("Can't convert " + s
                                  + " to an unsigned integer: it is negative");
  }
  return magnitude;
}

std::int64_t int_to_int64(const std::string & s)
{
  bool negative;
  std::uint64_t magnitude;
  parse_smtlib_int(s, negative, magnitude);
  const std::uint64_t max =
      static_cast<std::uint64_t>(std::numeric_limits<std::int64_t>::max());
  if (!negative && magnitude <= max)
  {
    return static_cast<std::int64_t>(magnitude);
  }
  if (negative && magnitude <= max)
  {
    return -static_cast<std::int64_t>(magnitude);
  }
  if (negative && magnitude == max + 1)
  {
    return std::numeric_limits<std::int64_t>::min();
  }
  throw IncorrectUsageException(
      "Can't convert " + s
      + " to a signed integer: it does not fit in 64 bits");
}

std::string bv_to_bits(const std::string & s)
{
  const std::string text = trim_spaces(s);
  std::string bits;
  if (text.substr(0, 2) == "#b")
  {
    bits = text.substr(2);
    if (bits.find_first_not_of("01") != std::string::npos)
    {
      throw not_a_bv_value(s);
    }
  }
  else if (text.substr(0, 2) == "#x")
  {
    for (char c : text.substr(2))
    {
      const unsigned d = numeral_digit(c);
      if (d >= 16)
      {
        throw not_a_bv_value(s);
      }
      for (unsigned i = 4; i-- > 0;)
      {
        bits.push_back((d >> i) & 1 ? '1' : '0');
      }
    }
  }
  else if (text.substr(0, 5) == "(_ bv" && text.back() == ')')
  {
    const std::string body = text.substr(5, text.size() - 6);
    const std::string::size_type space = body.find(' ');
    std::uint64_t width = 0;
    if (space == std::string::npos
        || !decimal_to_uint64(trim_spaces(body.substr(space + 1)), width))
    {
      throw not_a_bv_value(s);
    }
    const std::string numeral = body.substr(0, space);
    if (numeral.empty()
        || numeral.find_first_not_of("0123456789") != std::string::npos)
    {
      throw not_a_bv_value(s);
    }
    std::vector<std::uint32_t> words;
    try
    {
      words = value_words(numeral, 10, width);
    }
    catch (const IncorrectUsageException &)
    {
      // the numeral is at least 2^W
      throw not_a_bv_value(s);
    }
    bits.assign(width, '0');
    for (std::uint64_t i = 0; i < width; ++i)
    {
      if ((words[i / 32] >> (i % 32)) & 1)
      {
        bits[width - 1 - i] = '1';
      }
    }
  }
  if (bits.empty())
  {
    throw not_a_bv_value(s);
  }
  return bits;
}

std::uint64_t bv_to_uint64(const std::string & s)
{
  return low_64_bits(bv_to_bits(s), s);
}

std::int64_t bv_to_int64(const std::string & s)
{
  return low_64_bits_signed(bv_to_bits(s), s);
}

}  // namespace smtlib

}  // namespace smt
