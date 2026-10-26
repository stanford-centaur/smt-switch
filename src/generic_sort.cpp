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

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "exceptions.h"
#include "generic_datatype.h"
#include "smt_defs.h"
#include "sort.h"
#include "utils.h"

namespace smt {

/* smtlib representation of sort kinds, used only below */
static std::string to_smtlib(SortKind sk);

// implementations

GenericSort::GenericSort(SortKind k) : sk(k) {}

// Only used to make placeholder sorts for datatypes when the
// sort is the datatype itself but the sort hasn't been constructed.
GenericSort::GenericSort(std::string name)
    : sk(DATATYPE), datatype_name(std::move(name))
{
}

std::size_t GenericSort::hash() const { return str_hash(compute_string()); }

std::string GenericSort::to_string() const { return compute_string(); }

std::string GenericSort::compute_string() const
{
  if (get_sort_kind() == SortKind::ARRAY)
  {
    Sort index_sort = get_indexsort();
    Sort elem_sort = get_elemsort();
    std::string index_sort_str = index_sort->to_string();
    std::string elem_sort_str = elem_sort->to_string();
    return "(Array " + index_sort_str + " " + elem_sort_str + ")";
  }
  else if (get_sort_kind() == SortKind::BOOL)
  {
    return to_smtlib(SortKind::BOOL);
  }
  else if (get_sort_kind() == SortKind::BV)
  {
    return "(_ BitVec " + std::to_string(get_width()) + ")";
  }
  else if (get_sort_kind() == SortKind::INT)
  {
    return to_smtlib(SortKind::INT);
  }
  else if (get_sort_kind() == SortKind::REAL)
  {
    return to_smtlib(SortKind::REAL);
  }
  else if (get_sort_kind() == SortKind::FUNCTION)
  {
    std::string name = "(";
    std::vector<Sort> domain_sorts = get_domain_sorts();
    Sort codomain_sort = get_codomain_sort();
    int num_args = domain_sorts.size();
    for (int i = 0; i < num_args; i++)
    {
      if (i > 0)
      {
        name += " ";
      }
      name += domain_sorts[i]->to_string();
    }
    name += ") ";
    name += codomain_sort->to_string();
    return name;
  }
  else if (get_sort_kind() == SortKind::UNINTERPRETED)
  {
    if (get_arity() == 0)
    {
      return get_uninterpreted_name();
    }
    else
    {
      std::string result = "(" + get_uninterpreted_name();
      for (Sort s : get_uninterpreted_param_sorts())
      {
        result += " " + s->to_string();
      }
      return result + ")";
    }
  }
  else if (get_sort_kind() == SortKind::UNINTERPRETED_CONS)
  {
    return get_uninterpreted_name();
  }
  else if (get_sort_kind() == SortKind::DATATYPE)
  {
    // A placeholder from GenericSort(std::string) knows only the name it was
    // given: get_datatype throws for it, since only GenericDatatypeSort has
    // a datatype to return.
    if (!datatype_name.empty())
    {
      return datatype_name;
    }
    return get_generic_datatype()->get_name();
  }
  else if (get_sort_kind() == SortKind::CONSTRUCTOR
           || get_sort_kind() == SortKind::SELECTOR
           || get_sort_kind() == SortKind::TESTER)
  {
    return get_uninterpreted_name();
  }
  else
  {
    throw NotImplementedException("Can't print sort kind "
                                  + smt::to_string(get_sort_kind()));
  }
}

SortKind GenericSort::get_sort_kind() const { return sk; }

bool GenericSort::compare(const Sort & s) const
{
  // a sort of another solver is not this one, however alike
  if (!std::dynamic_pointer_cast<GenericSort>(s))
  {
    return false;
  }
  SortKind other_sk = s->get_sort_kind();
  if (sk != other_sk)
  {
    return false;
  }

  switch (sk)
  {
    case BOOL:
    case INT:
    case REAL:
    case STRING: {
      return true;
    }
    case BV: {
      return get_width() == s->get_width();
    }
    case ARRAY: {
      return (get_indexsort() == s->get_indexsort())
             && (get_elemsort() == s->get_elemsort());
    }
    case FUNCTION: {
      SortVec domain_sorts = get_domain_sorts();
      SortVec other_domain_sorts = s->get_domain_sorts();
      Sort return_sort = get_codomain_sort();
      Sort other_return_sort = s->get_codomain_sort();

      if (domain_sorts.size() != other_domain_sorts.size()
          || return_sort != other_return_sort)
      {
        return false;
      }

      for (std::size_t i = 0; i < domain_sorts.size(); i++)
      {
        if (domain_sorts[i] != other_domain_sorts[i])
        {
          return false;
        }
      }

      return true;
    }
    case UNINTERPRETED: {
      // every application of a constructor shares its name, so the
      // parameters tell them apart
      SortVec param_sorts = get_uninterpreted_param_sorts();
      SortVec other_param_sorts = s->get_uninterpreted_param_sorts();
      if (get_uninterpreted_name() != s->get_uninterpreted_name()
          || param_sorts.size() != other_param_sorts.size())
      {
        return false;
      }
      for (std::size_t i = 0; i < param_sorts.size(); i++)
      {
        if (param_sorts[i] != other_param_sorts[i])
        {
          return false;
        }
      }
      return true;
    }
    case UNINTERPRETED_CONS: {
      return get_uninterpreted_name() == s->get_uninterpreted_name()
             && get_arity() == s->get_arity();
    }
    case DATATYPE: {
      assert(sk == DATATYPE);
      std::shared_ptr<GenericDatatypeSort> other_type_cast =
          std::dynamic_pointer_cast<GenericDatatypeSort>(s);
      return other_type_cast
             && get_generic_datatype()->get_name()
                    == other_type_cast->compute_string();
    }
    case CONSTRUCTOR:
    case SELECTOR:
    case TESTER: {
      // the solver makes these only as DatatypeComponentSort, which
      // compares them itself
      return false;
    }
    case NUM_SORT_KINDS: {
      // null sorts should not be equal
      return false;
    }
  }
  throw SmtException("GenericSort comparison got an out-of-range SortKind "
                     + std::to_string(static_cast<int>(sk)));
}

std::uint64_t GenericSort::get_width() const
{
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no width");
}

std::size_t GenericSort::get_arity() const
{
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no arity");
}

Sort GenericSort::get_indexsort() const
{
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no index sort");
}

Sort GenericSort::get_elemsort() const
{
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no element sort");
}

SortVec GenericSort::get_domain_sorts() const
{
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no domain sorts");
}

Sort GenericSort::get_codomain_sort() const
{
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no codomain sort");
}

std::string GenericSort::get_uninterpreted_name() const
{
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no uninterpreted name");
}

std::vector<Sort> GenericSort::get_uninterpreted_param_sorts() const
{
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no uninterpreted param sorts");
}

Datatype GenericSort::get_datatype() const { return get_generic_datatype(); }

std::shared_ptr<GenericDatatype> GenericSort::get_generic_datatype() const
{
  if (!datatype_name.empty())
  {
    throw IncorrectUsageException("The sort of datatype " + datatype_name
                                  + " is not made yet");
  }
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no datatype");
}

const std::unordered_map<SortKind, std::string> sortkind2smtlib({
    { ARRAY, "Array" },
    { BOOL, "Bool" },
    { INT, "Int" },
    { REAL, "Real" },
});

static std::string to_smtlib(SortKind sk)
{
  assert(sortkind2smtlib.find(sk) != sortkind2smtlib.end());
  return sortkind2smtlib.at(sk);
}

BVGenericSort::BVGenericSort(std::uint64_t w) : GenericSort(BV), width(w) {}

std::uint64_t BVGenericSort::get_width() const { return width; }

// ArrayGenericSort

ArrayGenericSort::ArrayGenericSort(Sort idxsort, Sort esort)
    : GenericSort(ARRAY),
      indexsort(std::move(idxsort)),
      elemsort(std::move(esort))
{
}

Sort ArrayGenericSort::get_indexsort() const { return indexsort; }

Sort ArrayGenericSort::get_elemsort() const { return elemsort; }

// FunctionGenericSort

FunctionGenericSort::FunctionGenericSort(SortVec sorts, Sort rsort)
    : GenericSort(FUNCTION),
      domain_sorts(std::move(sorts)),
      codomain_sort(std::move(rsort))
{
}

SortVec FunctionGenericSort::get_domain_sorts() const { return domain_sorts; }

Sort FunctionGenericSort::get_codomain_sort() const { return codomain_sort; }

// UninterpretedGenericSort

UninterpretedGenericSort::UninterpretedGenericSort(std::string n,
                                                   std::uint64_t a)
    : GenericSort(a == 0 ? UNINTERPRETED : UNINTERPRETED_CONS),
      name(std::move(n)),
      arity(a)
{
}

UninterpretedGenericSort::UninterpretedGenericSort(Sort sort_cons,
                                                   const SortVec & sorts)
    : GenericSort(UNINTERPRETED),
      name(sort_cons->get_uninterpreted_name()),
      arity(sorts.size()),
      param_sorts(sorts)
{
  // compute_string prints the parameters only when the arity is non-zero, so
  // an applied sort keeps the count it was applied with, not the zero that
  // would hide both the name and the parameters.
  if (sort_cons->get_arity() != sorts.size())
  {
    throw IncorrectUsageException("Sort constructor " + name + " has arity "
                                  + std::to_string(sort_cons->get_arity())
                                  + " but was applied to "
                                  + std::to_string(sorts.size()) + " sorts");
  }
}

std::string UninterpretedGenericSort::get_uninterpreted_name() const
{
  return name;
}

std::size_t UninterpretedGenericSort::get_arity() const { return arity; }

SortVec UninterpretedGenericSort::get_uninterpreted_param_sorts() const
{
  return param_sorts;
}

GenericDatatypeSort::GenericDatatypeSort(std::shared_ptr<GenericDatatype> dt)
    : GenericSort(DATATYPE), gdt(std::move(dt))
{
}

std::shared_ptr<GenericDatatype> GenericDatatypeSort::get_generic_datatype()
    const
{
  return gdt;
}

std::string GenericDatatypeSort::compute_string() const
{
  return gdt->get_name();
}

bool GenericDatatypeSort::compare(const Sort & s) const
{
  // Compares the strings of two datatype sorts
  assert(s->get_sort_kind() == DATATYPE);
  std::shared_ptr<GenericDatatypeSort> other_sort =
      std::dynamic_pointer_cast<GenericDatatypeSort>(s);
  return other_sort && compute_string() == other_sort->to_string();
}

std::string GenericDatatypeSort::to_string() const
{
  return this->compute_string();
}

DatatypeComponentSort::DatatypeComponentSort(SortKind k, std::string n, Sort dt)
    : GenericSort(k),
      name(std::move(n)),
      dt_sort(backend_pointer_cast<GenericSort>(dt))
{
  if (k != CONSTRUCTOR && k != SELECTOR && k != TESTER)
  {
    throw IncorrectUsageException("Wrong sortkind input");
  }
}

bool DatatypeComponentSort::compare(const Sort & s) const
{
  // a component prints as its name, which is unique only within its
  // datatype
  std::shared_ptr<DatatypeComponentSort> other =
      std::dynamic_pointer_cast<DatatypeComponentSort>(s);
  return other && sk == other->sk && name == other->name
         && dt_sort == other->dt_sort;
}

std::size_t DatatypeComponentSort::hash() const
{
  // the name is unique only within the datatype, so mix in the datatype's
  // name and the kind, as compare checks both. Boost's hash_combine:
  // 0x9e3779b9 is 2^32 / golden ratio, whose irregular bits spread the
  // value; the shifts mix in the hash so far, so the order of the parts
  // matters and equal parts don't cancel out
  std::size_t h = str_hash(name);
  h ^= str_hash(dt_sort->to_string()) + 0x9e3779b9 + (h << 6) + (h >> 2);
  h ^= static_cast<std::size_t>(sk) + 0x9e3779b9 + (h << 6) + (h >> 2);
  return h;
}

std::string DatatypeComponentSort::compute_string() const { return name; }

std::string DatatypeComponentSort::to_string() const
{
  return compute_string();
}

SortVec DatatypeComponentSort::get_domain_sorts() const
{
  std::vector<Sort> domain_sorts;
  if (sk == CONSTRUCTOR)
  {
    std::shared_ptr<GenericDatatype> gdt = dt_sort->get_generic_datatype();
    for (int i = 0; i < gdt->get_num_constructors(); ++i)
    {
      std::shared_ptr<GenericDatatypeConstructorDecl> curr_con =
          std::static_pointer_cast<GenericDatatypeConstructorDecl>(
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
    return std::make_shared<GenericSort>(BOOL);
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
  return dt_sort->get_generic_datatype()->get_num_selectors(name);
}

}  // namespace smt
