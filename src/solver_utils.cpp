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

#include "solver_utils.h"

#include <cctype>
#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "exceptions.h"
#include "ops.h"
#include "solver.h"
#include "term.h"

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

unsigned detail::numeral_digit(char c)
{
  unsigned char u = static_cast<unsigned char>(c);
  if (!std::isalnum(u))
  {
    return 36;
  }
  return static_cast<unsigned>(std::isdigit(u) ? u - '0'
                                               : std::tolower(u) - 'a' + 10);
}

/** Whether s is a non-empty string of decimal digits */
static bool is_decimal_numeral(const std::string & s)
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
  if (base == 10)
  {
    return val;
  }
  if (base < 2 || base > 36)
  {
    throw IncorrectUsageException("Only accepted bases are 2 to 36, but got "
                                  + std::to_string(base));
  }
  unsigned b = static_cast<unsigned>(base);
  bool negative = val.find('-') == 0;
  std::string magnitude = negative ? val.substr(1) : val;
  std::string::size_type separator =
      sk == REAL ? magnitude.find_first_of("./") : std::string::npos;
  std::string whole = magnitude.substr(0, separator);
  std::string decimal = digits_to_decimal(whole, b);
  if (!decimal.empty() && separator != std::string::npos)
  {
    std::string part = magnitude.substr(separator + 1);
    std::string denominator;
    if (magnitude[separator] == '/')
    {
      denominator = digits_to_decimal(part, b);
    }
    else if (!part.empty())
    {
      // the digits after the point count base^-1, base^-2, ..., so the
      // number is all its digits over base^(digits after the point), a 1
      // followed by that many zeros
      decimal = digits_to_decimal(whole + part, b);
      denominator = digits_to_decimal("1" + std::string(part.size(), '0'), b);
    }
    decimal = decimal.empty() || denominator.empty()
                  ? ""
                  : decimal + "/" + denominator;
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

}  // namespace smt
