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

#include <iostream>
#include <string>
#include <unordered_map>

#include "exceptions.h"
#include "result.h"

namespace std
{
  // specialize the hash template
  template<>
  struct hash<smt::ResultType>
  {
    size_t operator()(const smt::ResultType r) const
    {
      return static_cast<std::size_t>(r);
    }
  };
}


namespace smt {

const std::unordered_map<ResultType, std::string> result2str(
    { { SAT, "sat" }, { UNSAT, "unsat" }, { UNKNOWN, "unknown" } });

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

std::string Result::to_string() const { return result2str.at(result); }

std::ostream & operator<<(std::ostream & output, const Result r)
{
  output << result2str.at(r.result);
  return output;
}

bool operator==(const Result & r1, const Result & r2)
{
  return r1.result == r2.result;
}

}  // namespace smt
