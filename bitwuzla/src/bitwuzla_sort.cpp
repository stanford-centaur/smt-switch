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

  // ask Aina about getting domain sorts from the sort
  throw SmtException("NYI");
}

// TODO implement all the methods -- starting with get_codomain_sorts (and
// finish previous domain sorts one)

}  // namespace smt
