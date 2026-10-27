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

#include "sort.h"

#include <cstddef>
#include <string>
#include <typeindex>
#include <typeinfo>
#include <unordered_map>

#include "datatype.h"
#include "exceptions.h"

namespace smt {

const std::unordered_map<SortKind, std::string> sortkind2str({
    { ARRAY, "Array" },
    { BOOL, "Bool" },
    { BV, "BitVec" },
    { INT, "Int" },
    { REAL, "Real" },
    { STRING, "String" },
    { FUNCTION, "Function" },
    { UNINTERPRETED, "Uninterpreted" },
    { UNINTERPRETED_CONS, "UninterpretedSortConstructor" },
    { DATATYPE, "Datatype" },
    { CONSTRUCTOR, "Constructor" },
    { SELECTOR, "Selector" },
    { TESTER, "Tester" },
});

std::string to_string(SortKind sk)
{
  if (sk == NUM_SORT_KINDS)
  {
    return "null";
  }
  return sortkind2str.at(sk);
}

// A null sort equals only another null sort
bool operator==(const Sort & s1, const Sort & s2)
{
  if (!s1 || !s2)
  {
    return !s1 && !s2;
  }
  return s1->compare(s2);
}

bool operator!=(const Sort & s1, const Sort & s2) { return !(s1 == s2); }

// Sorts have no id, so they order by the hash, which equal sorts share.
// Equal sorts can differ in kind and print (Boolector's Bool is its
// (_ BitVec 1), and a function sort its array sort), so a tie asks compare
// before the class, the printed sort, the kind and, for a datatype
// component, which prints as its name, its datatype's name, as compare
// checks it.
// Handles of two solvers of one backend never compare equal, but can tie
// on every key here, so the order is consistent only among the handles of
// one solver and its wrappers.
bool operator<(const Sort & s1, const Sort & s2)
{
  if (!s1 || !s2)
  {
    return !s1 && s2;
  }
  std::size_t h1 = s1->hash();
  std::size_t h2 = s2->hash();
  if (h1 != h2)
  {
    return h1 < h2;
  }
  if (s1 == s2)
  {
    return false;
  }
  const auto & o1 = *s1;
  const auto & o2 = *s2;
  std::type_index t1 = typeid(o1);
  std::type_index t2 = typeid(o2);
  if (t1 != t2)
  {
    return t1 < t2;
  }
  std::string str1 = s1->to_string();
  std::string str2 = s2->to_string();
  if (str1 != str2)
  {
    return str1 < str2;
  }
  SortKind k1 = s1->get_sort_kind();
  SortKind k2 = s2->get_sort_kind();
  if (k1 != k2)
  {
    return k1 < k2;
  }
  if (k1 != CONSTRUCTOR && k1 != SELECTOR && k1 != TESTER)
  {
    return false;
  }
  return s1->get_datatype()->get_name() < s2->get_datatype()->get_name();
}

bool operator>(const Sort & s1, const Sort & s2) { return s2 < s1; }
bool operator<=(const Sort & s1, const Sort & s2) { return !(s2 < s1); }
bool operator>=(const Sort & s1, const Sort & s2) { return !(s1 < s2); }

std::ostream & operator<<(std::ostream & output, const Sort s)
{
  output << (s ? s->to_string() : "null");
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
  else if (sk == STRING)
  {
    return "String";
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
    // an applied sort constructor prints with its parameters
    SortVec param_sorts = get_uninterpreted_param_sorts();
    if (param_sorts.empty())
    {
      return get_uninterpreted_name();
    }
    std::string res("(");
    res += get_uninterpreted_name();
    for (const Sort & s : param_sorts)
    {
      res += " ";
      res += s->to_string();
    }
    res += ")";
    return res;
  }
  else if (sk == UNINTERPRETED_CONS)
  {
    return get_uninterpreted_name();
  }
  else if (sk == DATATYPE)
  {
    return get_datatype()->get_name();
  }
  else
  {
    std::string msg("To string not implemented for SortKind = ");
    msg += smt::to_string(sk);
    throw NotImplementedException(msg);
  }
}

}  // namespace smt

namespace std {

size_t hash<smt::Sort>::operator()(const smt::Sort & s) const
{
  return s ? s->hash() : 0;
}

}  // namespace std
