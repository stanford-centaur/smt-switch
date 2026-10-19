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

#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <vector>

#include "bitwuzla/cpp/bitwuzla.h"
#include "smt.h"

namespace smt {

BzlaSort::BzlaSort(const bitwuzla::Sort s,
                   const std::shared_ptr<bitwuzla::TermManager> & tm)
    : tm(tm), sort(s)
{
}

BzlaSort::~BzlaSort()
{
  // TODO: figure out if sorts need to be destroyed
}

std::size_t BzlaSort::hash() const { return std::hash<bitwuzla::Sort>{}(sort); }

std::uint64_t BzlaSort::get_width() const { return sort.bv_size(); }

Sort BzlaSort::get_indexsort() const
{
  return std::make_shared<BzlaSort>(sort.array_index(), tm);
}

Sort BzlaSort::get_elemsort() const
{
  return std::make_shared<BzlaSort>(sort.array_element(), tm);
}

SortVec BzlaSort::get_domain_sorts() const
{
  std::vector<bitwuzla::Sort> bsorts = sort.fun_domain();
  SortVec domain_sorts;
  domain_sorts.reserve(bsorts.size());

  for (auto && bsort : bsorts)
  {
    domain_sorts.push_back(std::make_shared<BzlaSort>(bsort, tm));
  }

  return domain_sorts;
}

Sort BzlaSort::get_codomain_sort() const
{
  return std::make_shared<BzlaSort>(sort.fun_codomain(), tm);
}

std::string BzlaSort::get_uninterpreted_name() const
{
  return sort.uninterpreted_symbol().value_or("");
}

std::size_t BzlaSort::get_arity() const
{
  if (sort.is_uninterpreted())
  {
    return 0;
  }
  throw IncorrectUsageException(
      "Sort of kind " + smt::to_string(get_sort_kind()) + " has no arity");
}

SortVec BzlaSort::get_uninterpreted_param_sorts() const
{
  // Bitwuzla has no sort constructors, so no sort has parameters
  if (get_sort_kind() == UNINTERPRETED)
  {
    return {};
  }
  throw IncorrectUsageException(
      "Can only get param sorts from uninterpreted sort");
}

Datatype BzlaSort::get_datatype() const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

bool BzlaSort::compare(const Sort & s) const
{
  std::shared_ptr<BzlaSort> bsort = std::static_pointer_cast<BzlaSort>(s);
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
  else if (sort.is_fp())
  {
    return REAL;
  }
  else if (sort.is_bool())
  {
    return BOOL;
  }
  else if (sort.is_uninterpreted())
  {
    return UNINTERPRETED;
  }
  else
  {
    throw SmtException("Got Bitwuzla sort of unknown SortKind.");
  }
}

}  // namespace smt
