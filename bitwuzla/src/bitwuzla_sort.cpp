/*********************                                                        */
/*! \file bitwuzla_sort.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bitwuzla implementation of AbsSort
**
**
**/

#include "bitwuzla_sort.h"

#include "assert.h"
#include "bitwuzla/cpp/bitwuzla.h"
#include "sort.h"

using namespace std;

namespace smt {

BzlaSort::~BzlaSort()
{
  // TODO: figure out if sorts need to be destroyed
}

size_t BzlaSort::hash() const { return std::hash<bitwuzla::Sort>{}(sort); }

uint64_t BzlaSort::get_width() const { return sort.bv_size(); }

Sort BzlaSort::get_indexsort() const
{
  return make_shared<BzlaSort>(sort.array_index());
}

Sort BzlaSort::get_elemsort() const
{
  return make_shared<BzlaSort>(sort.array_element());
}

SortVec BzlaSort::get_domain_sorts() const
{
  size_t arity;
  std::vector<bitwuzla::Sort> bsorts = sort.fun_domain();
  SortVec domain_sorts; domain_sorts.reserve(arity);

  for (auto&& bsort : bsorts)
  {
    domain_sorts.push_back(make_shared<BzlaSort>(bsort));
  }

  return domain_sorts;
}

Sort BzlaSort::get_codomain_sort() const
{
  return make_shared<BzlaSort>(sort.fun_codomain());
}

std::string BzlaSort::get_uninterpreted_name() const
{
  throw IncorrectUsageException(
      "Bitwuzla does not support uninterpreted sorts.");
}

size_t BzlaSort::get_arity() const { return sort.fun_arity(); }

SortVec BzlaSort::get_uninterpreted_param_sorts() const
{
  throw SmtException("Bitwuzla does not support uninterpreted sorts.");
}

Datatype BzlaSort::get_datatype() const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

bool BzlaSort::compare(const Sort & s) const
{
  shared_ptr<BzlaSort> bsort = static_pointer_cast<BzlaSort>(s);
  return sort == bsort->sort;
}

SortKind BzlaSort::get_sort_kind() const
{
  if (sort.is_bv())
  {
    return BV;
  }
  else if (sort.is_array())
  {
    return ARRAY;
  }
  else if (sort.is_fun())
  {
    return FUNCTION;
  }
  else if (sort.is_fp()) {
    return REAL;
  }
  else if (sort.is_bool()) {
    return BOOL;
  }
  else if (sort.is_uninterpreted()) {
    return UNINTERPRETED;
  }
  else
  {
    throw SmtException("Got Bitwuzla sort of unknown SortKind.");
  }
}

}  // namespace smt
