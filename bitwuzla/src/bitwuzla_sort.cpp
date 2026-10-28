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

#include <bitwuzla/cpp/bitwuzla.h>

#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "exceptions.h"

namespace smt {

BzlaSort::BzlaSort(bitwuzla::Sort s,
                   const std::shared_ptr<bitwuzla::TermManager> & manager)
    : tm(manager), sort(std::move(s))
{
}

std::size_t BzlaSort::hash() const { return std::hash<bitwuzla::Sort>{}(sort); }

std::uint64_t BzlaSort::get_width() const
{
  if (!sort.is_bv())
  {
    throw IncorrectUsageException(
        "Sort of kind " + smt::to_string(get_sort_kind()) + " has no width");
  }
  return sort.bv_size();
}

Sort BzlaSort::get_indexsort() const
{
  if (!sort.is_array())
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no index sort");
  }
  return std::make_shared<BzlaSort>(sort.array_index(), tm);
}

Sort BzlaSort::get_elemsort() const
{
  if (!sort.is_array())
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no element sort");
  }
  return std::make_shared<BzlaSort>(sort.array_element(), tm);
}

SortVec BzlaSort::get_domain_sorts() const
{
  if (!sort.is_fun())
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no domain sorts");
  }
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
  if (!sort.is_fun())
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no codomain sort");
  }
  return std::make_shared<BzlaSort>(sort.fun_codomain(), tm);
}

std::string BzlaSort::get_uninterpreted_name() const
{
  if (!sort.is_uninterpreted())
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no uninterpreted name");
  }
  return sort.uninterpreted_symbol().value_or("");
}

std::size_t BzlaSort::get_arity() const
{
  if (!sort.is_uninterpreted())
  {
    throw IncorrectUsageException(
        "Sort of kind " + smt::to_string(get_sort_kind()) + " has no arity");
  }
  return 0;
}

SortVec BzlaSort::get_uninterpreted_param_sorts() const
{
  if (!sort.is_uninterpreted())
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no uninterpreted param sorts");
  }
  // Bitwuzla has no sort constructors, so no sort has parameters
  return {};
}

Datatype BzlaSort::get_datatype() const
{
  // Bitwuzla has no datatypes, so no sort has a datatype
  throw IncorrectUsageException(
      "Sort of kind " + smt::to_string(get_sort_kind()) + " has no datatype");
}

bool BzlaSort::compare(const Sort & s) const
{
  std::shared_ptr<BzlaSort> bsort = std::dynamic_pointer_cast<BzlaSort>(s);
  return bsort && sort == bsort->sort;
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

const bitwuzla::Sort BzlaSort::get_bitwuzla_sort() const { return sort; }

}  // namespace smt
