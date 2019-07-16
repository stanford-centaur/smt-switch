#include <array>
#include <iostream>
#include <string>

#include "result.h"

namespace smt
{
/**
   This function should only be called once, to generate the constexpr
   sortcon2str for converting enums to string_views.
*/
constexpr std::array<std::string_view, NUM_RESULTS> generate_result2str()
{
  std::array<std::string_view, NUM_RESULTS> result2str;

  result2str[SAT] = std::string_view("sat");
  result2str[UNSAT] = std::string_view("unsat");
  result2str[UNKNOWN] = std::string_view("unknown");
  return result2str;
}

constexpr std::array<std::string_view, NUM_RESULTS> result2str =
  generate_result2str();

std::string Result::to_string() const
{
  return std::string(result2str[result]);
}

std::ostream & operator<<(std::ostream & output, const Result r)
{
  output << result2str[r.result];
  return output;
}

}
