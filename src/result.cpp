/*********************                                                        */
/*! \file result.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief The result of a call to check-sat or check-sat-assuming.
**
**
**/

#include "result.h"

#include <string>
#include <utility>

#include "exceptions.h"

namespace smt {

Result::Result(ResultType rt, std::string reason)
    : result(rt), explanation(std::move(reason))
{
}

bool Result::is_sat() const { return result == SAT; }

bool Result::is_unsat() const { return result == UNSAT; }

bool Result::is_unknown() const { return result == UNKNOWN; }

bool Result::is_null() const { return result == NUM_RESULTS; }

std::string Result::get_explanation() const
{
  if (result != UNKNOWN)
  {
    throw IncorrectUsageException(
        "Result was not unknown. Cannot get explanation");
  }
  else
  {
    return explanation;
  }
}

std::string Result::to_string() const
{
  switch (result)
  {
    case SAT: return "sat";
    case UNSAT: return "unsat";
    case UNKNOWN: return "unknown";
    case NUM_RESULTS: break;
  }
  throw SmtException("Result::to_string got a ResultType with no name: "
                     + std::to_string(static_cast<int>(result)));
}

std::ostream & operator<<(std::ostream & output, const Result r)
{
  output << r.to_string();
  return output;
}

bool operator==(const Result & r1, const Result & r2)
{
  return r1.result == r2.result;
}

bool operator!=(const Result & r1, const Result & r2) { return !(r1 == r2); }

}  // namespace smt
