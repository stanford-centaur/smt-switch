/*********************                                                        */
/*! \file yices2_sort.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Yices2 implementation of AbsSort
**
**
**/

#include "yices2_sort.h"

#include <yices.h>

#include <cstdint>
#include <memory>

#include "exceptions.h"
#include "yices2_datatype.h"

using namespace std;

namespace smt {

// Yices2Sort implementation

Yices2Sort::Yices2Sort(type_t y_type, bool is_fun)
    : type(y_type), is_function(is_fun)
{
}

std::size_t Yices2Sort::hash() const
{
  // type_t is a unique id, see Yices2 docs.
  return type;
}

uint64_t Yices2Sort::get_width() const
{
  if (!yices_type_is_bitvector(type))
  {
    throw IncorrectUsageException(
        "Sort of kind " + smt::to_string(get_sort_kind()) + " has no width");
  }
  return (unsigned int)yices_bvtype_size(type);
}

Sort Yices2Sort::get_indexsort() const
{
  if (get_sort_kind() != ARRAY)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no index sort");
  }
  return Sort(new Yices2Sort(yices_type_child(type, 0)));
}

Sort Yices2Sort::get_elemsort() const
{
  if (get_sort_kind() != ARRAY)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no element sort");
  }
  return Sort(new Yices2Sort(yices_type_child(type, 1)));
}

SortVec Yices2Sort::get_domain_sorts() const
{
  if (get_sort_kind() != FUNCTION)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no domain sorts");
  }
  // one less because last is return sort.
  int32_t s_arity = yices_type_num_children(type) - 1;
  SortVec sorts;
  sorts.reserve(s_arity);

  for (int32_t i = 0; i < s_arity; i++)
  {
    sorts.push_back(Sort(new Yices2Sort(yices_type_child(type, i))));
  }

  return sorts;
}

Sort Yices2Sort::get_codomain_sort() const
{
  if (get_sort_kind() != FUNCTION)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no codomain sort");
  }
  // The last element of the result of num_children is the range/codomain
  // type.
  return Sort(new Yices2Sort(
      yices_type_child(type, yices_type_num_children(type) - 1)));
}

string Yices2Sort::get_uninterpreted_name() const
{
  if (get_sort_kind() != UNINTERPRETED)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no uninterpreted name");
  }
  const char * res = yices_get_type_name(type);
  if (res == NULL)
  {
    throw InternalSolverException("Failed to get name of uninterpreted sort");
  }
  return res;
}

size_t Yices2Sort::get_arity() const
{
  if (get_sort_kind() != UNINTERPRETED)
  {
    throw IncorrectUsageException(
        "Sort of kind " + smt::to_string(get_sort_kind()) + " has no arity");
  }
  // yices2 does not support uninterpreted sorts with non-zero arity
  return 0;
}

SortVec Yices2Sort::get_uninterpreted_param_sorts() const
{
  if (get_sort_kind() != UNINTERPRETED)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no uninterpreted param sorts");
  }
  // Yices2 has no sort constructors, so no sort has parameters
  return {};
}

Datatype Yices2Sort::get_datatype() const
{
  if (get_sort_kind() != DATATYPE)
  {
    throw IncorrectUsageException(
        "Sort of kind " + smt::to_string(get_sort_kind()) + " has no datatype");
  }
  return std::make_shared<Yices2Datatype>(type);
};

bool Yices2Sort::compare(const Sort & s) const
{
  shared_ptr<Yices2Sort> ys = std::dynamic_pointer_cast<Yices2Sort>(s);
  return ys && type == ys->type;
}

SortKind Yices2Sort::get_sort_kind() const
{
  if (yices_type_is_int(type))
  {
    return INT;
  }
  else if (yices_type_is_real(type))
  {
    return REAL;
  }
  else if (yices_type_is_bool(type))
  {
    return BOOL;
  }
  else if (yices_type_is_bitvector(type))
  {
    return BV;
  }
  else if (yices_type_is_function(type))
  {
    // Test if array or actually function.
    // This may not be the most effective way to do this.
    if (!is_function)
    {
      return ARRAY;
    }
    else
    {
      return FUNCTION;
    }
  }
  else if (yices_type_is_uninterpreted(type))
  {
    return UNINTERPRETED;
  }
  else if (yices_type_is_scalar(type))
  {
    // only make_datatype_sorts makes scalar types, each one an enumeration
    return DATATYPE;
  }
  else
  {
    std::string msg("Unknown Yices2 type: ");
    msg += yices_type_to_string(type, 120, 1, 0);
    throw NotImplementedException(msg.c_str());
  }
}

type_t Yices2Sort::get_ytype() const { return type; }

}  // namespace smt
