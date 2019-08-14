#include <array>
#include <sstream>

#include "sort.h"
#include "utils.h"

namespace smt {

/**
   This function should only be called once, to generate the constexpr
   sortcon2str for converting enums to string_views.
*/
constexpr std::array<std::string_view, NUM_SORT_CONS> generate_sortcon2str()
{
  std::array<std::string_view, NUM_SORT_CONS> sortcon2str;

  sortcon2str[ARRAY] = std::string_view("ARRAY");
  sortcon2str[BOOL] = std::string_view("BOOL");
  sortcon2str[BV] = std::string_view("BV");
  sortcon2str[INT] = std::string_view("INT");
  sortcon2str[REAL] = std::string_view("REAL");
  sortcon2str[FUNCTION] = std::string_view("FUNCTION");

  return sortcon2str;
}

constexpr std::array<std::string_view, NUM_SORT_CONS> sortcon2str =
    generate_sortcon2str();

std::string to_string(SortCon sc) { return std::string(sortcon2str[sc]); }

bool operator==(const Sort & s1, const Sort & s2) { return s1->compare(s2); }

std::ostream & operator<<(std::ostream & output, const Sort s)
{
  output << s->to_string();
  return output;
}

}  // namespace smt
