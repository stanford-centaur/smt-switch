/*********************                                                        */
/*! \file boolector_sort.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Boolector implementation of AbsSort
**
**
**/

#include "boolector_sort.h"

#include <boolector.h>

#include <cstdint>
#include <functional>
#include <utility>

#include "exceptions.h"

namespace smt {

/* BoolectorSortBase implementation */

BoolectorSortBase::BoolectorSortBase(SortKind k,
                                     const std::shared_ptr<Btor> & b,
                                     BoolectorSort s)
    : btor(b), sort(s), sk(k)
{
}

BoolectorSortBase::~BoolectorSortBase()
{
  boolector_release_sort(btor.get(), sort);
}

std::size_t BoolectorSortBase::hash() const
{
  return std::hash<BoolectorSort>{}(sort);
}

// by default the following get_* methods don't work
// overloaded in derived classes
uint64_t BoolectorSortBase::get_width() const
{
  throw IncorrectUsageException(
      "Sort of kind " + smt::to_string(get_sort_kind()) + " has no width");
}

Sort BoolectorSortBase::get_indexsort() const
{
  throw IncorrectUsageException(
      "Sort of kind " + smt::to_string(get_sort_kind()) + " has no index sort");
}

Sort BoolectorSortBase::get_elemsort() const
{
  throw IncorrectUsageException("Sort of kind "
                                + smt::to_string(get_sort_kind())
                                + " has no element sort");
}

SortVec BoolectorSortBase::get_domain_sorts() const
{
  throw IncorrectUsageException("Sort of kind "
                                + smt::to_string(get_sort_kind())
                                + " has no domain sorts");
}

Sort BoolectorSortBase::get_codomain_sort() const
{
  throw IncorrectUsageException("Sort of kind "
                                + smt::to_string(get_sort_kind())
                                + " has no codomain sort");
}

std::string BoolectorSortBase::get_uninterpreted_name() const
{
  // Boolector has no uninterpreted sorts, so no sort has an uninterpreted name
  throw IncorrectUsageException("Sort of kind "
                                + smt::to_string(get_sort_kind())
                                + " has no uninterpreted name");
}

size_t BoolectorSortBase::get_arity() const
{
  // Boolector has no uninterpreted sorts, so no sort has an arity
  throw IncorrectUsageException(
      "Sort of kind " + smt::to_string(get_sort_kind()) + " has no arity");
}

SortVec BoolectorSortBase::get_uninterpreted_param_sorts() const
{
  // Boolector has no uninterpreted sorts, so no sort has param sorts
  throw IncorrectUsageException("Sort of kind "
                                + smt::to_string(get_sort_kind())
                                + " has no uninterpreted param sorts");
}

Datatype BoolectorSortBase::get_datatype() const
{
  // Boolector has no datatypes, so no sort has a datatype
  throw IncorrectUsageException(
      "Sort of kind " + smt::to_string(get_sort_kind()) + " has no datatype");
}

bool BoolectorSortBase::compare(const Sort & s) const
{
  std::shared_ptr<BoolectorSortBase> bs =
      std::dynamic_pointer_cast<BoolectorSortBase>(s);
  return bs && sort == bs->sort;
}

SortKind BoolectorSortBase::get_sort_kind() const { return sk; }

BoolectorSort BoolectorSortBase::get_btor_sort() const { return sort; }

BoolectorBVSort::BoolectorBVSort(const std::shared_ptr<Btor> & b,
                                 BoolectorSort s,
                                 uint64_t w)
    : BoolectorSortBase(BV, b, s), width(w)
{
}

BoolectorArraySort::BoolectorArraySort(const std::shared_ptr<Btor> & b,
                                       BoolectorSort s,
                                       Sort is,
                                       Sort es)
    : BoolectorSortBase(ARRAY, b, s),
      indexsort(std::move(is)),
      elemsort(std::move(es))
{
}

BoolectorUFSort::BoolectorUFSort(const std::shared_ptr<Btor> & b,
                                 BoolectorSort s,
                                 SortVec sorts,
                                 Sort codomain)
    : BoolectorSortBase(FUNCTION, b, s),
      domain_sorts(std::move(sorts)),
      codomain_sort(std::move(codomain))
{
}

SortVec BoolectorUFSort::get_domain_sorts() const { return domain_sorts; }

Sort BoolectorUFSort::get_codomain_sort() const { return codomain_sort; }

uint64_t BoolectorBVSort::get_width() const { return width; }

Sort BoolectorArraySort::get_indexsort() const { return indexsort; }

Sort BoolectorArraySort::get_elemsort() const { return elemsort; }
/* end BoolectorSolver implementation */

}  // namespace smt
