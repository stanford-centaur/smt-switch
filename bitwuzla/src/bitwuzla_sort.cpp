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

using namespace std;

namespace smt {

size_t BitwuzlaSort::hash() const { return bitwuzla_sort_hash(bzla, sort); }

uint64_t BitwuzlaSort::get_width() const
{
  return bitwuzla_sort_bv_get_size(bzla, sort);
}

Sort BitwuzlaSort::get_indexsort() const
{
  return make_shared<BitwuzlaSort>(bzla,
                                   bitwuzla_sort_array_get_index(bzla, sort));
}

Sort BitwuzlaSort::get_elemsort() const
{
  return make_shared<BitwuzlaSort>(bzla,
                                   bitwuzla_sort_array_get_element(bzla, sort));
}

SortVec BitwuzlaSort::get_domain_sorts() const
{
  uint32_t arity = bitwuzla_sort_fun_get_arity(bzla, sort);
  SortVec domain_sorts;
  domain_sorts.reserve(arity);

  const BitwuzlaSort * bsorts = bitwuzla_sort_fun_get_domain_sort(bzla, sort);

  for (size_t i = 0; i < arity; ++i)
  {
    // array is zero-terminated -- shouldn't hit the end
    assert(bsorts);
    domain_sorts.push_back(make_shared<BitwuzlaSort>(bzla, *bsorts));
    ++bsorts;
  }
  // should be at end of the array
  assert(bsort);

  return domain_sorts;
}

Sort BitwuzlaSort::get_codomain_sort() const
{
  return make_shared<BitwuzlaSort>(bzla,
                                   bitwuzla_sort_fun_get_codomain(bzla, sort));
}

std::string BitwuzlaSort::get_uninterpreted_name() const
{
  throw IncorrectUsageException(
      "Bitwuzla does not support uninterpreted sorts.");
}

Datatype BitwuzlaSort::get_datatype() const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

bool BitwuzlaSort::compare(const Sort s)
{
  shared_ptr<BitwuzlaSort> bsort = static_pointer_cast<BitwuzlaSort>(s);
  return bitwuzla_sort_is_equal(bzla, sort, bsort);
}

SortKind BitwuzlaSort::get_sort_kind() const
{
  if (bitwuzla_sort_is_bv(bzla, sort))
  {
    return BV;
  }
  else if (bitwuzla_sort_is_array(bzla, sort))
  {
    return ARRAY;
  }
  else if (bitwuzla_sort_is_fun(bzla, sort))
  {
    return FUNCTION;
  }
  else
  {
    throw SmtException("Got Bitwuzla sort of unknown SortKind.");
  }
}

}  // namespace smt
