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

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <string>

#include "exceptions.h"
#include "ops.h"
#include "solver.h"
#include "term.h"

namespace smt {

Term make_nary_term(const AbsSmtSolver * solver,
                    const Op & op,
                    const TermVec & terms)
{
  assert(terms.size() >= 2);
  std::size_t size = terms.size();
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

std::uint32_t narrow_index(const Op & op, std::uint64_t idx)
{
  if (idx > std::numeric_limits<std::uint32_t>::max())
  {
    throw IncorrectUsageException("Index " + std::to_string(idx) + " of "
                                  + op.to_string()
                                  + " does not fit in the 32 bits this solver "
                                    "accepts");
  }
  return static_cast<std::uint32_t>(idx);
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

}  // namespace smt
