/*********************                                                        */
/*! \file cvc4_sort.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief CVC4 implementation of AbsSort
**
**
**/

#include "exceptions.h"

#include "cvc4_sort.h"
#include "cvc4_datatype.h"

namespace smt {

// struct for hashing
CVC4::api::SortHashFunction sorthash;

std::string CVC4Sort::to_string() const
{
  return sort.toString();
}

std::size_t CVC4Sort::hash() const
{
  return sorthash(sort);
}

uint64_t CVC4Sort::get_width() const { return sort.getBVSize(); }

Sort CVC4Sort::get_indexsort() const
{
  return std::make_shared<CVC4Sort> (sort.getArrayIndexSort());
}

Sort CVC4Sort::get_elemsort() const
{
  return std::make_shared<CVC4Sort> (sort.getArrayElementSort());
}

SortVec CVC4Sort::get_domain_sorts() const
{
  std::vector<::CVC4::api::Sort> cvc4_sorts = sort.getFunctionDomainSorts();
  SortVec domain_sorts;
  domain_sorts.reserve(cvc4_sorts.size());
  Sort s;
  for (auto cs : cvc4_sorts)
  {
    s.reset(new CVC4Sort(cs));
    domain_sorts.push_back(s);
  }
  return domain_sorts;
}

Sort CVC4Sort::get_codomain_sort() const
{
  return std::make_shared<CVC4Sort> (sort.getFunctionCodomainSort());
}

std::string CVC4Sort::get_uninterpreted_name() const { return sort.toString(); }

size_t CVC4Sort::get_arity() const
{
  try
  {
    if (sort.isUninterpretedSort())
    {
      return 0;
    }
    else
    {
      return sort.getSortConstructorArity();
    }
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

SortVec CVC4Sort::get_uninterpreted_param_sorts() const
{
  SortVec param_sorts;
  for (auto cs : sort.getUninterpretedSortParamSorts())
  {
    param_sorts.push_back(std::make_shared<CVC4Sort>(cs));
  }
  return param_sorts;
}

bool CVC4Sort::compare(const Sort & s) const
{
  std::shared_ptr<CVC4Sort> cs = std::static_pointer_cast<CVC4Sort>(s);
  return sort == cs->sort;
}

Datatype CVC4Sort::get_datatype() const
{
  try
  {
    return std::make_shared<CVC4Datatype>(sort.getDatatype());
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
};

SortKind CVC4Sort::get_sort_kind() const
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
  else if (sort.isSortConstructor())
  {
    return UNINTERPRETED_CONS;
  }
  else if (sort.isDatatype())
  {
    return DATATYPE;
  }
  else if (sort.isConstructor())
  {
    return CONSTRUCTOR;
  }
  else if (sort.isSelector())
  {
    return SELECTOR;
  }
  else if (sort.isTester())
  {
    return TESTER;
  }
  else
  {
    throw NotImplementedException("Unknown kind in CVC4 translation.");
  }
}

}
