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

#include <functional>
#include <unordered_map>

#include "assert.h"
#include "generic_datatype.h"
#include "utils.h"
using namespace std;

namespace smt {

Sort make_uninterpreted_generic_sort(string name, uint64_t arity)
{
  return make_shared<UninterpretedGenericSort>(name, arity);
}

Sort make_uninterpreted_generic_sort(Sort sort_cons,
                                     const SortVec & sorts) {
  return make_shared<UninterpretedGenericSort>(sort_cons, sorts);
}


Sort make_generic_sort(SortKind sk)
{
  if (sk != BOOL && sk != INT && sk != REAL)
  {
    throw IncorrectUsageException("Can't create sort from " + to_string(sk));
  }
  return make_shared<GenericSort>(sk);
}

Sort make_generic_sort(SortKind sk, uint64_t width)
{
  if (sk != BV)
  {
    throw IncorrectUsageException("Can't create sort from " + to_string(sk)
                                  + " and " + ::std::to_string(width));
  }
  return make_shared<BVGenericSort>(width);
}

Sort make_generic_sort(SortKind sk, Sort sort1)
{
  throw IncorrectUsageException(
      "No currently supported sort is created with a single sort argument");
}

Sort make_generic_sort(SortKind sk, Sort sort1, Sort sort2)
{
  Sort genericsort;
  if (sk == ARRAY)
  {
    genericsort = make_shared<ArrayGenericSort>(sort1, sort2);
  }
  else if (sk == FUNCTION)
  {
    genericsort =
        make_shared<FunctionGenericSort>(SortVec{ sort1 }, sort2);
  }
  else
  {
    throw IncorrectUsageException("Can't make sort from " + to_string(sk) + " "
                                  + sort1->to_string() + " "
                                  + sort2->to_string());
  }
  return genericsort;
}

Sort make_generic_sort(SortKind sk, Sort sort1, Sort sort2, Sort sort3)
{
  if (sk == FUNCTION)
  {
    return make_shared<FunctionGenericSort>(
        SortVec{ sort1, sort2 }, sort3);
  }
  else
  {
    throw IncorrectUsageException(
        "Can't make sort from " + to_string(sk) + " " + sort1->to_string() + " "
        + sort2->to_string() + " " + sort3->to_string());
  }
}

Sort make_generic_sort(SortKind sk, SortVec sorts)
{
  if (sk == FUNCTION)
  {
    Sort return_sort = sorts.back();
    sorts.pop_back();
    return make_shared<FunctionGenericSort>(sorts, return_sort);
  }
  else if (sk == ARRAY && sorts.size() == 2)
  {
    return make_shared<ArrayGenericSort>(sorts[0], sorts[1]);
  }
  else
  {
    string msg("Can't make sort from ");
    msg += to_string(sk);
    for (auto ss : sorts)
    {
      msg += " " + ss->to_string();
    }
    throw IncorrectUsageException(msg);
  }
}

Sort make_generic_sort(Datatype dt)
{
  return make_shared<GenericDatatypeSort>(dt);
}
Sort make_generic_sort(SortKind sk, std::string cons_name, Sort dt)
{
  return make_shared<DatatypeComponentSort>(sk, cons_name, dt);
}

// implementations

GenericSort::GenericSort(SortKind sk) : sk(sk) {}

// Only used to make placeholder sorts for datatypes when the
// sort is the datatype itself but the sort hasn't been constructed.
GenericSort::GenericSort(std::string name) : sk(DATATYPE) {}

GenericSort::~GenericSort() {}

size_t GenericSort::hash() const { 
  return str_hash(compute_string());
}

string GenericSort::to_string() const {
  return compute_string();
}

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
    }
    else if (get_sort_kind() == SortKind::DATATYPE)
    {
      return static_pointer_cast<GenericDatatype>(get_datatype())->get_name();
    }
    else if (get_sort_kind() == SortKind::CONSTRUCTOR
             || get_sort_kind() == SortKind::SELECTOR
             || get_sort_kind() == SortKind::TESTER)
    {
      return get_uninterpreted_name();
    }
    else
    {
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
      assert(sk == DATATYPE);
      shared_ptr<GenericDatatypeSort> other_type_cast =
          static_pointer_cast<GenericDatatypeSort>(s);
      return static_pointer_cast<GenericDatatype>(get_datatype())->get_name()
             == other_type_cast->compute_string();
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
          "Hit default case in GenericSort comparison -- missing a SortCon");
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


BVGenericSort::BVGenericSort(uint64_t width)
    : GenericSort(BV), width(width)
{
}

BVGenericSort::~BVGenericSort() {}

uint64_t BVGenericSort::get_width() const { return width; }

// ArrayGenericSort

ArrayGenericSort::ArrayGenericSort(Sort idxsort, Sort esort)
    : GenericSort(ARRAY), indexsort(idxsort), elemsort(esort)
{
}

ArrayGenericSort::~ArrayGenericSort() {}

Sort ArrayGenericSort::get_indexsort() const { return indexsort; }

Sort ArrayGenericSort::get_elemsort() const { return elemsort; }

// FunctionGenericSort

FunctionGenericSort::FunctionGenericSort(SortVec sorts, Sort rsort)
    : GenericSort(FUNCTION), domain_sorts(sorts), codomain_sort(rsort)
{
}

FunctionGenericSort::~FunctionGenericSort() {}

SortVec FunctionGenericSort::get_domain_sorts() const
{
  return domain_sorts;
}

Sort FunctionGenericSort::get_codomain_sort() const { return codomain_sort; }

// UninterpretedGenericSort

UninterpretedGenericSort::UninterpretedGenericSort(string n, uint64_t a)
    : GenericSort(a == 0 ? UNINTERPRETED : UNINTERPRETED_CONS), name(n), arity(a)
{
}

UninterpretedGenericSort::UninterpretedGenericSort(Sort sort_cons, const SortVec& sorts)
    : GenericSort(UNINTERPRETED), name(""), arity(0), param_sorts(sorts)
{
  assert(sort_cons->get_arity() == sorts.size());
}


UninterpretedGenericSort::~UninterpretedGenericSort() {}

std::string UninterpretedGenericSort::get_uninterpreted_name() const
{
  return name;
}

size_t UninterpretedGenericSort::get_arity() const { return arity; }

SortVec UninterpretedGenericSort::get_uninterpreted_param_sorts() const
{
  return param_sorts;
}

GenericDatatypeSort::GenericDatatypeSort(const Datatype & dt)
    : GenericSort(DATATYPE), gdt(dt)
{
}

GenericDatatypeSort::~GenericDatatypeSort() {}

Datatype GenericDatatypeSort::get_datatype() const { return gdt; }

std::string GenericDatatypeSort::compute_string() const
{
  return static_pointer_cast<GenericDatatype>(gdt)->get_name();
}

bool GenericDatatypeSort::compare(const Sort & s) const
{
  // Compares the strings of two datatype sorts
  assert(s->get_sort_kind() == DATATYPE);
  shared_ptr<GenericDatatypeSort> other_sort =
      static_pointer_cast<GenericDatatypeSort>(s);
  return compute_string() == other_sort->to_string();
}

std::string GenericDatatypeSort::to_string() const
{
  return this->compute_string();
}

DatatypeComponentSort::DatatypeComponentSort(SortKind sk,
                                             std::string name,
                                             Sort dt)
    : GenericSort(sk), name(name), dt_sort(dt)
{
  if (sk != CONSTRUCTOR && sk != SELECTOR && sk != TESTER)
  {
    throw IncorrectUsageException("Wrong sortkind input");
  }
}
std::string DatatypeComponentSort::compute_string() const { return name; }

std::string DatatypeComponentSort::to_string() const
{
  return compute_string();
}

std::string DatatypeComponentSort::get_uninterpreted_name() const
{
  return name;
}

SortVec DatatypeComponentSort::get_domain_sorts() const
{
  std::vector<Sort> domain_sorts;
  if (sk == CONSTRUCTOR)
  {
    shared_ptr<GenericDatatypeSort> cast_dt_sort =
        static_pointer_cast<GenericDatatypeSort>(dt_sort);
    shared_ptr<GenericDatatype> gdt =
        static_pointer_cast<GenericDatatype>(cast_dt_sort->get_datatype());
    for (int i = 0; i < gdt->get_num_constructors(); ++i)
    {
      shared_ptr<GenericDatatypeConstructorDecl> curr_con =
          static_pointer_cast<GenericDatatypeConstructorDecl>(
              gdt->get_cons_vector()[i]);
      if (curr_con->get_name() == name)
      {
        for (int f = 0; f < curr_con->get_selector_count(); ++f)
        {
          domain_sorts.push_back(curr_con->get_selector_vector()[f].sort);
        }
      }
    }
  }
  else
  {
    domain_sorts.push_back(dt_sort);
  }
  return domain_sorts;
}

Sort DatatypeComponentSort::get_codomain_sort() const
{
  if (sk == CONSTRUCTOR)
  {
    return dt_sort;
  }
  else if (sk == TESTER)
  {
    return make_generic_sort(BOOL);
  }
  else if (sk == SELECTOR)
  {
    return selector_sort;
  }

  assert(sk == CONSTRUCTOR || sk == TESTER || sk == SELECTOR);

  return nullptr;
}

void DatatypeComponentSort::set_selector_sort(Sort new_selector_sort)
{
  selector_sort = new_selector_sort;
}

int DatatypeComponentSort::get_num_selectors() const
{
  shared_ptr<GenericDatatype> dt =
      static_pointer_cast<GenericDatatype>(dt_sort->get_datatype());
  return dt->get_num_selectors(name);
}

Datatype DatatypeComponentSort::get_datatype() const
{
  return dt_sort->get_datatype();
}

}  // namespace smt
