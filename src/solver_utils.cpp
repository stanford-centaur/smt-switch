/*********************                                                        */
/*! \file solver_utils.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Utility functions for solver implementations. Meant for internal
**        use only, not from the API.
**
**/

#include "smt-switch/solver_utils.h"

#include <fcntl.h>
#include <unistd.h>

#include <algorithm>
#include <cerrno>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/solver.h"
#include "smt-switch/term.h"

namespace smt {

Term make_nary_term(const AbsSmtSolver * solver,
                    const Op & op,
                    const TermVec & terms)
{
  std::size_t size = terms.size();
  if (size < 2)
  {
    throw IncorrectUsageException("Can't apply " + op.to_string() + " to "
                                  + std::to_string(size) + " terms.");
  }
  if (is_left_assoc(op.prim_op))
  {
    Term res = terms[0];
    for (std::size_t i = 1; i < size; ++i)
    {
      res = solver->make_term(op, res, terms[i]);
    }
    return res;
  }
  else if (is_right_assoc(op.prim_op))
  {
    Term res = terms[size - 1];
    for (std::size_t i = 1; i < size; ++i)
    {
      res = solver->make_term(op, terms[size - 1 - i], res);
    }
    return res;
  }

  TermVec conjuncts;
  if (is_chainable(op.prim_op))
  {
    for (std::size_t i = 0; i + 1 < size; ++i)
    {
      conjuncts.push_back(solver->make_term(op, terms[i], terms[i + 1]));
    }
  }
  else if (is_pairwise(op.prim_op))
  {
    for (std::size_t i = 0; i < size; ++i)
    {
      for (std::size_t j = i + 1; j < size; ++j)
      {
        conjuncts.push_back(solver->make_term(op, terms[i], terms[j]));
      }
    }
  }
  else
  {
    throw IncorrectUsageException("Can't apply " + op.to_string() + " to "
                                  + std::to_string(size) + " terms.");
  }
  return conjuncts.size() == 1 ? conjuncts[0]
                               : solver->make_term(And, conjuncts);
}

void check_quantifier_binders(const Op & op, const TermVec & terms)
{
  if (terms.size() < 2)
  {
    throw IncorrectUsageException(op.to_string()
                                  + " takes one or more params and a body");
  }
  for (std::size_t i = 0; i + 1 < terms.size(); ++i)
  {
    if (!terms[i]->is_param())
    {
      throw IncorrectUsageException(op.to_string() + " can only bind a param, "
                                    + "but got " + terms[i]->to_string());
    }
  }
}

std::uint32_t narrow_index(const Op & op, std::uint64_t idx)
{
  if (!detail::fits_in<std::uint32_t>(idx))
  {
    throw IncorrectUsageException("Index " + std::to_string(idx) + " of "
                                  + op.to_string()
                                  + " does not fit in the 32 bits this solver "
                                    "accepts");
  }
  return static_cast<std::uint32_t>(idx);
}

std::uint32_t narrow_width(std::uint64_t width)
{
  return detail::narrow<std::uint32_t>(width, "a bit-vector width");
}

std::uint32_t narrow_levels(std::uint64_t levels)
{
  return detail::narrow<std::uint32_t>(levels, "a number of levels");
}

std::uint32_t narrow_num_args(std::size_t num_args)
{
  return detail::narrow<std::uint32_t>(num_args, "a number of arguments");
}

bool bool_option_value(const std::string & option, const std::string & value)
{
  if (value != "true" && value != "false")
  {
    throw IncorrectUsageException("The option " + option
                                  + " takes true or false, not " + value);
  }
  return value == "true";
}

double time_limit_seconds(const std::string & value)
{
  double seconds = 0;
  std::size_t end = 0;
  try
  {
    seconds = std::stod(value, &end);
  }
  catch (const std::logic_error &)
  {
    // std::stod failed, so end is still zero
  }
  if (end == 0 || end != value.size() || !std::isfinite(seconds) || seconds < 0)
  {
    throw IncorrectUsageException(
        "The option time-limit takes a nonnegative number of seconds, not "
        + value);
  }
  // Half of what a clock counting nanoseconds in 64 bits holds, so that a
  // solver adding the limit to the time now cannot overflow; a longer limit
  // is as good as none.
  constexpr double longest =
      std::chrono::duration<double>(std::chrono::nanoseconds::max()).count()
      / 2;
  return std::min(seconds, longest);
}

std::uint64_t time_limit_milliseconds(const std::string & value)
{
  // time_limit_seconds keeps the limit far below 2^64 milliseconds.
  return static_cast<std::uint64_t>(time_limit_seconds(value) * 1000);
}

unsigned detail::numeral_digit(char c)
{
  return static_cast<unsigned>(c >= '0' && c <= '9'   ? c - '0'
                               : c >= 'a' && c <= 'z' ? c - 'a' + 10
                               : c >= 'A' && c <= 'Z' ? c - 'A' + 10
                                                      : 36);
}

/** The exception for a val that is not a base-`base` numeral */
static IncorrectUsageException not_a_numeral(const std::string & val,
                                             std::uint64_t base)
{
  return IncorrectUsageException("Value " + val + " is not a base-"
                                 + std::to_string(base) + " numeral");
}

std::vector<std::uint32_t> detail::bv_value_to_words(const std::string & val,
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

std::uint64_t detail::bv_value_to_uint64(const std::string & val,
                                         std::uint64_t base,
                                         std::uint64_t width)
{
  std::vector<std::uint32_t> words = bv_value_to_words(val, base, width);
  return words.size() > 1 ? std::uint64_t{ words[1] } << 32 | words[0]
                          : words[0];
}

bool is_decimal_numeral(const std::string & s)
{
  return !s.empty() && s.find_first_not_of("0123456789") == std::string::npos;
}

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

/** The decimal numeral of the non-empty string of base-`base` digits
 *  `digits`, 0 to 9 then a to z in either case, or "" if digits is not one
 */
static std::string digits_to_decimal(const std::string & digits, unsigned base)
{
  if (digits.empty())
  {
    return "";
  }
  std::string dec = "0";
  for (char c : digits)
  {
    unsigned digit = detail::numeral_digit(c);
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

std::string arith_value_to_decimal(SortKind sk,
                                   const std::string & val,
                                   std::uint64_t base)
{
  bool negative = val.find('-') == 0;
  std::string magnitude = negative || val.find('+') == 0 ? val.substr(1) : val;
  if (base == 10)
  {
    // a second sign is left in, for the caller's check to refuse
    return negative || magnitude.find_first_of("+-") == 0 ? val : magnitude;
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

UnorderedTermMap store_chain_values(
    const std::vector<std::pair<Term, Term>> & stores)
{
  UnorderedTermMap assignments;
  for (const auto & store : stores)
  {
    // insert keeps the assignment already in the map, so the outermost
    // store, which comes first, is the one that stands
    assignments.insert(store);
  }
  return assignments;
}

int detail::make_cloexec_pipe(int (&fds)[2])
{
  // pipe2 would set the flag in the same call, but macOS lacks it.
  if (pipe(fds) != 0)
  {
    fds[0] = -1;
    fds[1] = -1;
    return errno;
  }
  for (int fd : fds)
  {
    if (fcntl(fd, F_SETFD, FD_CLOEXEC) != 0)
    {
      int fcntl_errno = errno;
      close(fds[0]);
      close(fds[1]);
      fds[0] = -1;
      fds[1] = -1;
      return fcntl_errno;
    }
  }
  return 0;
}

}  // namespace smt
