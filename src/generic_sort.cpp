/*********************                                                        */
/*! \file generic_sort.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class that represents a sort for generic solver.
**
**/

#include "generic_sort.h"
#include <unordered_map>
#include <functional>
#include "assert.h"
#include "utils.h"
using namespace std;

namespace smt {

GenericSort::GenericSort(SortKind sk) : sk(sk) {}

GenericSort::~GenericSort() {}

size_t GenericSort::hash() const { 
  return str_hash(compute_string());
}

string GenericSort::to_string() const {
  return compute_string();

string GenericSort::compute_string() const {
    if (get_sort_kind() == SortKind::ARRAY) {
      Sort index_sort = get_indexsort();
      Sort elem_sort = get_elemsort();
      std::string index_sort_str = index_sort->to_string();
      std::string elem_sort_str = elem_sort->to_string();
      return "(Array " + index_sort_str + " " + elem_sort_str + ")";
    } else if (get_sort_kind() == SortKind::BOOL) {
      return smt::to_smtlib(SortKind::BOOL);
    } else if (get_sort_kind() == SortKind::BV) {
       return string("(_ BitVec ") + std::to_string(get_width()) + string(")");
    } else if (get_sort_kind() == SortKind::INT) {
      return smt::to_smtlib(SortKind::INT);
    } else if (get_sort_kind() == SortKind::REAL) {
      return smt::to_smtlib(SortKind::REAL);
    } else if (get_sort_kind() == SortKind::FUNCTION) {
      string name = "(";
      vector<Sort> domain_sorts = get_domain_sorts();
      Sort codomain_sort = get_codomain_sort();
      int num_args = domain_sorts.size();
      for (int i=0; i<num_args; i++) {
        name += domain_sorts[i]->to_string();
      }
      name += ") ";
      name += codomain_sort->to_string();
      return name;
    } else if (get_sort_kind() == SortKind::UNINTERPRETED) {
      if (get_arity() == 0) {
        return get_uninterpreted_name();
      } else {
        std::string result = "(" + get_uninterpreted_name();
        for (Sort s : get_uninterpreted_param_sorts()) {
          result += " " + s->to_string();
        }
        return result;
      }
    } else if (get_sort_kind() == SortKind::UNINTERPRETED_CONS) {
      return get_uninterpreted_name();
    } else {
      assert(false);
    }
}


SortKind GenericSort::get_sort_kind() const { return sk; }

bool GenericSort::compare(const Sort & s) const
{
  SortKind other_sk = s->get_sort_kind();
  if (sk != other_sk)
  {
    return false;
  }

  switch (sk)
  {
    case BOOL:
    case INT:
    case REAL: { return true;
    }
    case BV: { return get_width() == s->get_width();
    }
    case ARRAY:
    {
      return (get_indexsort() == s->get_indexsort())
             && (get_elemsort() == s->get_elemsort());
    }
    case FUNCTION:
    {
      SortVec domain_sorts = get_domain_sorts();
      SortVec other_domain_sorts = s->get_domain_sorts();
      Sort return_sort = get_codomain_sort();
      Sort other_return_sort = s->get_codomain_sort();

      if (domain_sorts.size() != other_domain_sorts.size()
          || return_sort != other_return_sort)
      {
        return false;
      }

      for (size_t i = 0; i < domain_sorts.size(); i++)
      {
        if (domain_sorts[i] != other_domain_sorts[i])
        {
          return false;
        }
      }

      return true;
    }
    case UNINTERPRETED:
    {
      return get_uninterpreted_name() == s->get_uninterpreted_name();
    }
    case DATATYPE:
    {
      throw NotImplementedException("StatefulSort::compare");
    }
    case NUM_SORT_KINDS:
    {
      // null sorts should not be equal
      return false;
    }
    default:
    {
      // this code should be unreachable
      throw SmtException(
          "Hit default case in StatefulSort comparison -- missing a SortCon");
    }
  }
}

const std::unordered_map<SortKind, std::string> sortkind2smtlib(
    { { ARRAY, "Array" },
      { BOOL, "Bool" },
      { INT, "Int" },
      { REAL, "Real" }});

std::string to_smtlib(SortKind sk)
{
  assert(sortkind2smtlib.find(sk) != sortkind2smtlib.end());
  return sortkind2smtlib.at(sk);
}

}  // namespace smt
