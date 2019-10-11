#include <array>
#include <sstream>

#include "exceptions.h"
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

std::string to_string(SortKind sk)
{
  if (sk == NUM_SORT_CONS)
  {
    return "null";
  }
  return std::string(sortcon2str[sk]);
}

bool operator==(const Sort & s1, const Sort & s2) { return s1->compare(s2); }

bool operator!=(const Sort & s1, const Sort & s2) { return !s1->compare(s2); }

std::ostream & operator<<(std::ostream & output, const Sort s)
{
  output << s->to_string();
  return output;
}

std::string AbsSort::to_string() const
{
  SortKind sk = get_sort_kind();
  if (sk == NUM_SORT_CONS)
  {
    return "nullsort";
  }
  else if (sk == BOOL)
  {
    return "Bool";
  }
  else if (sk == INT)
  {
    return "Int";
  }
  else if (sk == REAL)
  {
    return "Real";
  }
  else if (sk == BV)
  {
    std::string res("(_ BitVec ");
    res += std::to_string(get_width());
    res += ")";
    return res;
  }
  else if (sk == ARRAY)
  {
    std::string res("(Array ");
    res += get_indexsort()->to_string();
    res += " ";
    res += get_elemsort()->to_string();
    res += ")";
    return res;
  }
  else if (sk == FUNCTION)
  {
    std::string res("(");
    for (auto arg : get_domain_sorts())
    {
      res += " ";
      res += arg->to_string();
    }
    res += ") -> (";
    res += get_codomain_sort()->to_string();
    res += ")";
    return res;
  }
  else
  {
    std::string msg("To string not implemented for SortKind = ");
    msg += ::smt::to_string(sk);
    throw NotImplementedException(msg);
  }
}

}  // namespace smt
