/*!
 * \file result.cpp
 * \brief The result of a call to check-sat or check-sat-assuming
 * \author Makai Mann
 * \author Clark Barrett
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/result.h"

#include <string>
#include <utility>

#include "smt-switch/exceptions.h"

namespace smt {

Result::Result(Kind kind, std::string explanation)
    : kind_(kind), explanation_(std::move(explanation))
{
}

Result Result::sat() { return Result(Kind::Sat, "no explanation"); }

Result Result::unsat() { return Result(Kind::Unsat, "no explanation"); }

Result Result::unknown(std::string explanation)
{
  return Result(Kind::Unknown, std::move(explanation));
}

bool Result::is_sat() const { return kind_ == Kind::Sat; }

bool Result::is_unsat() const { return kind_ == Kind::Unsat; }

bool Result::is_unknown() const { return kind_ == Kind::Unknown; }

bool Result::is_null() const { return kind_ == Kind::Null; }

std::string Result::get_explanation() const
{
  if (kind_ != Kind::Unknown)
  {
    throw IncorrectUsageException(
        "Result was not unknown. Cannot get explanation");
  }
  return explanation_;
}

std::string Result::to_string() const
{
  switch (kind_)
  {
    case Kind::Sat: return "sat";
    case Kind::Unsat: return "unsat";
    case Kind::Unknown: return "unknown";
    case Kind::Null: break;
  }
  throw InternalException("Result::to_string got a Result with no name: "
                          + std::to_string(static_cast<int>(kind_)));
}

std::ostream & operator<<(std::ostream & output, const Result r)
{
  output << r.to_string();
  return output;
}

bool operator==(const Result & r1, const Result & r2)
{
  return r1.kind_ == r2.kind_;
}

bool operator!=(const Result & r1, const Result & r2) { return !(r1 == r2); }

}  // namespace smt
