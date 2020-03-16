#include <iostream>
#include <string>
#include <unordered_map>

#include "result.h"

namespace smt {

const std::unordered_map<ResultType, std::string> result2str(
    { { SAT, "sat" }, { UNSAT, "unsat" }, { UNKNOWN, "unknown" } });

std::string Result::to_string() const { return result2str.at(result); }

std::ostream & operator<<(std::ostream & output, const Result r)
{
  output << result2str.at(r.result);
  return output;
}

}  // namespace smt
