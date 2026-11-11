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
#include "utils.h"

namespace smt {

BzlaSort::BzlaSort(bitwuzla::Sort s,
                   const std::shared_ptr<BzlaTermManager> & manager)
    : tm(manager), sort(std::move(s))
{
}

BzlaSort::BzlaSort(std::uint64_t constructor,
                   const std::shared_ptr<BzlaTermManager> & manager)
    : tm(manager), sort(), is_constructor(true), constructor_id(constructor)
{
}

std::size_t BzlaSort::hash() const
{
  if (is_constructor)
  {
    std::size_t h = std::hash<BzlaTermManager *>{}(tm.get());
    detail::hash_combine(h, constructor_id);
    return h;
  }
  return std::hash<bitwuzla::Sort>{}(sort);
}

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
  SortKind sk = get_sort_kind();
  if (sk == UNINTERPRETED_CONS)
  {
    return tm->get_constructor_name(constructor_id);
  }
  if (sk == UNINTERPRETED)
  {
    // an applied sort is named after its constructor, not its Bitwuzla sort
    return tm->get_instance_name(sort);
  }
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no uninterpreted name");
}

std::size_t BzlaSort::get_arity() const
{
  SortKind sk = get_sort_kind();
  if (sk == UNINTERPRETED_CONS)
  {
    return tm->get_constructor_arity(constructor_id);
  }
  if (sk == UNINTERPRETED)
  {
    return 0;
  }
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no arity");
}

Sort BzlaSort::get_uninterpreted_constructor() const
{
  if (get_sort_kind() != UNINTERPRETED || !tm->is_instance(sort))
  {
    throw IncorrectUsageException("Sort " + to_string()
                                  + " was not made by applying a sort "
                                    "constructor");
  }
  return std::make_shared<BzlaSort>(tm->get_instance_constructor(sort), tm);
}

SortVec BzlaSort::get_uninterpreted_param_sorts() const
{
  if (get_sort_kind() != UNINTERPRETED)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no uninterpreted param sorts");
  }
  auto bzla_params = tm->get_instance_params(sort);
  SortVec params;
  params.reserve(bzla_params.size());
  for (const bitwuzla::Sort & p : bzla_params)
  {
    params.push_back(std::make_shared<BzlaSort>(p, tm));
  }
  return params;
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
  if (!bsort || is_constructor != bsort->is_constructor)
  {
    return false;
  }
  if (is_constructor)
  {
    // Bitwuzla makes a distinct sort for each declaration, so each
    // constructor is distinct too, even from one of the same name
    return tm == bsort->tm && constructor_id == bsort->constructor_id;
  }
  return sort == bsort->sort;
}

SortKind BzlaSort::get_sort_kind() const
{
  if (is_constructor)
  {
    return UNINTERPRETED_CONS;
  }
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
    throw SmtException(
        "Failed to translate a Bitwuzla sort to an smt-switch sort");
  }
}

const bitwuzla::Sort BzlaSort::get_bitwuzla_sort() const
{
  if (is_constructor)
  {
    throw IncorrectUsageException("Sort constructor "
                                  + tm->get_constructor_name(constructor_id)
                                  + " is not a term sort until it is applied");
  }
  return sort;
}

}  // namespace smt
