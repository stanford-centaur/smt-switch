/*********************                                                        */
/*! \file cvc5_sort.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief cvc5 implementation of AbsSort
**
**
**/

#include "cvc5_sort.h"

#include <cvc5/cvc5.h>

#include <cstdint>
#include <memory>
#include <vector>

#include "cvc5_datatype.h"
#include "exceptions.h"

namespace smt {

// struct for hashing
std::hash<cvc5::Sort> sorthash;

Cvc5Sort::Cvc5Sort(::cvc5::Sort s) : sort(s) {}

std::string Cvc5Sort::to_string() const { return sort.toString(); }

std::size_t Cvc5Sort::hash() const { return sorthash(sort); }

uint64_t Cvc5Sort::get_width() const
{
  if (!sort.isBitVector())
  {
    throw IncorrectUsageException(
        "Sort of kind " + smt::to_string(get_sort_kind()) + " has no width");
  }
  return sort.getBitVectorSize();
}

Sort Cvc5Sort::get_indexsort() const
{
  if (!sort.isArray())
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no index sort");
  }
  return std::make_shared<Cvc5Sort>(sort.getArrayIndexSort());
}

Sort Cvc5Sort::get_elemsort() const
{
  if (!sort.isArray())
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no element sort");
  }
  return std::make_shared<Cvc5Sort>(sort.getArrayElementSort());
}

SortVec Cvc5Sort::get_domain_sorts() const
{
  // cvc5 has a separate accessor for each kind of sort with a domain
  std::vector<::cvc5::Sort> cvc5_sorts;
  if (sort.isFunction())
  {
    cvc5_sorts = sort.getFunctionDomainSorts();
  }
  else if (sort.isDatatypeConstructor())
  {
    cvc5_sorts = sort.getDatatypeConstructorDomainSorts();
  }
  else if (sort.isDatatypeSelector())
  {
    cvc5_sorts = { sort.getDatatypeSelectorDomainSort() };
  }
  else if (sort.isDatatypeTester())
  {
    cvc5_sorts = { sort.getDatatypeTesterDomainSort() };
  }
  else
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no domain sorts");
  }
  SortVec domain_sorts;
  domain_sorts.reserve(cvc5_sorts.size());
  Sort s;
  for (auto cs : cvc5_sorts)
  {
    s.reset(new Cvc5Sort(cs));
    domain_sorts.push_back(s);
  }
  return domain_sorts;
}

Sort Cvc5Sort::get_codomain_sort() const
{
  if (sort.isFunction())
  {
    return std::make_shared<Cvc5Sort>(sort.getFunctionCodomainSort());
  }
  if (sort.isDatatypeConstructor())
  {
    return std::make_shared<Cvc5Sort>(
        sort.getDatatypeConstructorCodomainSort());
  }
  if (sort.isDatatypeSelector())
  {
    return std::make_shared<Cvc5Sort>(sort.getDatatypeSelectorCodomainSort());
  }
  if (sort.isDatatypeTester())
  {
    return std::make_shared<Cvc5Sort>(sort.getDatatypeTesterCodomainSort());
  }
  throw IncorrectUsageException("Sort of kind "
                                + smt::to_string(get_sort_kind())
                                + " has no codomain sort");
}

std::string Cvc5Sort::get_uninterpreted_name() const
{
  // an applied sort prints with its parameters, but is named after its
  // constructor
  if (sort.isUninterpretedSort() && sort.isInstantiated())
  {
    return sort.getUninterpretedSortConstructor().toString();
  }
  if (sort.isUninterpretedSort() || sort.isUninterpretedSortConstructor())
  {
    return sort.toString();
  }
  throw IncorrectUsageException("Sort of kind "
                                + smt::to_string(get_sort_kind())
                                + " has no uninterpreted name");
}

size_t Cvc5Sort::get_arity() const
{
  if (sort.isUninterpretedSort())
  {
    return 0;
  }
  if (sort.isUninterpretedSortConstructor())
  {
    return sort.getUninterpretedSortConstructorArity();
  }
  throw IncorrectUsageException(
      "Sort of kind " + smt::to_string(get_sort_kind()) + " has no arity");
}

SortVec Cvc5Sort::get_uninterpreted_param_sorts() const
{
  if (!sort.isUninterpretedSort())
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no uninterpreted param sorts");
  }
  // cvc5 refuses getInstantiatedParameters on a sort that was not applied
  if (!sort.isInstantiated())
  {
    return {};
  }
  SortVec param_sorts;
  for (auto cs : sort.getInstantiatedParameters())
  {
    param_sorts.push_back(std::make_shared<Cvc5Sort>(cs));
  }
  return param_sorts;
}

bool Cvc5Sort::compare(const Sort & s) const
{
  std::shared_ptr<Cvc5Sort> cs = std::dynamic_pointer_cast<Cvc5Sort>(s);
  return cs && sort == cs->sort;
}

Datatype Cvc5Sort::get_datatype() const
{
  return std::make_shared<Cvc5Datatype>(get_cvc5_datatype());
};

::cvc5::Sort Cvc5Sort::get_cvc5_sort() const { return sort; }

::cvc5::Datatype Cvc5Sort::get_cvc5_datatype() const
{
  if (!sort.isDatatype())
  {
    throw IncorrectUsageException(
        "Sort of kind " + smt::to_string(get_sort_kind()) + " has no datatype");
  }
  return sort.getDatatype();
}

SortKind Cvc5Sort::get_sort_kind() const
{
  if (sort.isBoolean())
  {
    return BOOL;
  }
  else if (sort.isBitVector())
  {
    return BV;
  }
  else if (sort.isInteger())
  {
    return INT;
  }
  else if (sort.isReal())
  {
    return REAL;
  }
  else if (sort.isString())
  {
    return STRING;
  }
  else if (sort.isArray())
  {
    return ARRAY;
  }
  else if (sort.isFunction())
  {
    return FUNCTION;
  }
  else if (sort.isUninterpretedSort())
  {
    return UNINTERPRETED;
  }
  else if (sort.isUninterpretedSortConstructor())
  {
    return UNINTERPRETED_CONS;
  }
  else if (sort.isDatatype())
  {
    return DATATYPE;
  }
  else if (sort.isDatatypeConstructor())
  {
    return CONSTRUCTOR;
  }
  else if (sort.isDatatypeSelector())
  {
    return SELECTOR;
  }
  else if (sort.isDatatypeTester())
  {
    return TESTER;
  }
  else
  {
    throw NotImplementedException("Unknown kind in cvc5 translation.");
  }
}

}  // namespace smt
