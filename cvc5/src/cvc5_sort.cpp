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

#include "cvc5_datatype.h"
#include "exceptions.h"

namespace smt {

// struct for hashing
std::hash<cvc5::Sort> sorthash;

std::string Cvc5Sort::to_string() const { return sort.toString(); }

std::size_t Cvc5Sort::hash() const { return sorthash(sort); }

uint64_t Cvc5Sort::get_width() const { return sort.getBitVectorSize(); }

Sort Cvc5Sort::get_indexsort() const
{
  return std::make_shared<Cvc5Sort>(sort.getArrayIndexSort());
}

Sort Cvc5Sort::get_elemsort() const
{
  return std::make_shared<Cvc5Sort>(sort.getArrayElementSort());
}

SortVec Cvc5Sort::get_domain_sorts() const
{
  std::vector<::cvc5::Sort> cvc5_sorts = sort.getFunctionDomainSorts();
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
  return std::make_shared<Cvc5Sort>(sort.getFunctionCodomainSort());
}

std::string Cvc5Sort::get_uninterpreted_name() const { return sort.toString(); }

size_t Cvc5Sort::get_arity() const
{
  try
  {
    if (sort.isUninterpretedSort())
    {
      return 0;
    }
    else
    {
      return sort.getUninterpretedSortConstructorArity();
    }
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

SortVec Cvc5Sort::get_uninterpreted_param_sorts() const
{
  SortVec param_sorts;
  for (auto cs : sort.getInstantiatedParameters())
  {
    param_sorts.push_back(std::make_shared<Cvc5Sort>(cs));
  }
  return param_sorts;
}

bool Cvc5Sort::compare(const Sort & s) const
{
  std::shared_ptr<Cvc5Sort> cs = std::static_pointer_cast<Cvc5Sort>(s);
  return sort == cs->sort;
}

Datatype Cvc5Sort::get_datatype() const
{
  try
  {
    return std::make_shared<Cvc5Datatype>(sort.getDatatype());
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
};

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
