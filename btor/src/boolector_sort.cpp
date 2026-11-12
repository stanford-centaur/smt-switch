/*!
 * \file boolector_sort.cpp
 * \brief Boolector implementation of AbsSort
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/boolector_sort.h"

#include <boolector.h>

#include <cstddef>
#include <cstdint>
#include <functional>
#include <utility>

#include "smt-switch/exceptions.h"
#include "smt-switch/utils.h"

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
  // Boolector numbers sorts per instance, so mix in the instance, as compare
  // checks it
  std::size_t h = std::hash<Btor *>{}(btor.get());
  detail::hash_combine(h, sort);
  return h;
}

// by default the following get_* methods don't work
// overloaded in derived classes
std::uint64_t BoolectorSortBase::get_width() const
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

std::size_t BoolectorSortBase::get_arity() const
{
  // Boolector has no uninterpreted sorts, so no sort has an arity
  throw IncorrectUsageException(
      "Sort of kind " + smt::to_string(get_sort_kind()) + " has no arity");
}

Sort BoolectorSortBase::get_uninterpreted_constructor() const
{
  // Boolector has no uninterpreted sorts, so no sort was made by applying a
  // sort constructor
  throw IncorrectUsageException("Sort " + to_string()
                                + " was not made by applying a sort "
                                  "constructor");
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
  return bs && btor == bs->btor && sort == bs->sort;
}

SortKind BoolectorSortBase::get_sort_kind() const { return sk; }

BoolectorSort BoolectorSortBase::get_btor_sort() const { return sort; }

BoolectorBVSort::BoolectorBVSort(const std::shared_ptr<Btor> & b,
                                 BoolectorSort s,
                                 std::uint64_t w)
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

std::uint64_t BoolectorBVSort::get_width() const { return width; }

Sort BoolectorArraySort::get_indexsort() const { return indexsort; }

Sort BoolectorArraySort::get_elemsort() const { return elemsort; }
/* end BoolectorSolver implementation */

}  // namespace smt
