#include <sstream>
#include <unordered_map>

#include "exceptions.h"
#include "sort.h"
#include "utils.h"

namespace std
{
  // specialize the hash template
  template<>
  struct hash<smt::SortKind>
  {
    size_t operator()(const smt::SortKind sk) const
    {
      return static_cast<std::size_t>(sk);
    }
  };
}


namespace smt {

const std::unordered_map<SortKind, std::string> sortkind2str(
    { { ARRAY, "ARRAY" },
      { BOOL, "BOOL" },
      { BV, "BV" },
      { INT, "INT" },
      { REAL, "REAL" },
      { FUNCTION, "FUNCTION" } });

std::string to_string(SortKind sk)
{
  if (sk == NUM_SORT_CONS)
  {
    return "null";
  }
  return sortkind2str.at(sk);
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
