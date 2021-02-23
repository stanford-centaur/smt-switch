/*********************                                                        */
/*! \file sort.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Abstract interface for SMT sorts.
**
**
**/

#include <sstream>
#include <unordered_map>

#include "exceptions.h"
#include "sort.h"
#include "utils.h"

namespace smt {

const std::unordered_map<SortKind, std::string> sortkind2str(
    { { ARRAY, "ARRAY" },
      { BOOL, "BOOL" },
      { BV, "BV" },
      { INT, "INT" },
      { REAL, "REAL" },
      { FUNCTION, "FUNCTION" },
      { UNINTERPRETED, "UNINTERPRETED" },
      { UNINTERPRETED_CONS, "UNINTERPRETED_CONS" },
      { DATATYPE, "DATATYPE" } });

std::string to_string(SortKind sk)
{
  if (sk == NUM_SORT_KINDS)
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
  if (sk == NUM_SORT_KINDS)
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
  else if (sk == UNINTERPRETED)
  {
    return get_uninterpreted_name();
  }
  else
  {
    std::string msg("To string not implemented for SortKind = ");
    msg += ::smt::to_string(sk);
    throw NotImplementedException(msg);
  }
}

}  // namespace smt
