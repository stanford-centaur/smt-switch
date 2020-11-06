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
#include <sstream>
#include "exceptions.h"

using namespace std;

namespace smt {

// Yices2Sort implementation

std::size_t Yices2Sort::hash() const
{
  // type_t is a unique id, see Yices2 docs.
  return type;
}

uint64_t Yices2Sort::get_width() const
{
  size_t out_width;
  if (yices_type_is_bitvector(type))
  {
    return (unsigned int)yices_bvtype_size(type);
  }
  else
  {
    throw IncorrectUsageException("Can only get width from bit-vector sort");
  }
}

Sort Yices2Sort::get_indexsort() const
{
  // Arrays are functions in Yices.
  if (yices_type_is_function(type))
  {
    return Sort(new Yices2Sort(yices_type_child(type, 0)));
  }
  else
  {
    throw IncorrectUsageException("Can only get index sort from array sort");
  }
}

Sort Yices2Sort::get_elemsort() const
{
  // Arrays are functions in Yices.
  if (yices_type_is_function(type))
  {
    return Sort(new Yices2Sort(yices_type_child(type, 1)));
  }
  else
  {
    throw IncorrectUsageException("Can only get element sort from array sort");
  }
}

SortVec Yices2Sort::get_domain_sorts() const
{
  if (yices_type_is_function(type))
  {
    // one less because last is return sort.
    int32_t s_arity = yices_type_num_children(type) - 1;
    SortVec sorts;
    sorts.reserve(s_arity);

    for (size_t i = 0; i < s_arity; i++)
    {
      sorts.push_back(Sort(new Yices2Sort(yices_type_child(type, i))));
    }

    return sorts;
  }
  else
  {
    throw IncorrectUsageException(
        "Can't get domain sorts from non-function sort.");
  }
}

Sort Yices2Sort::get_codomain_sort() const
{
  if (yices_type_is_function(type))
  {
    // The last element of the result of num_children is the range/codomain
    // type.
    return Sort(new Yices2Sort(
        yices_type_child(type, yices_type_num_children(type) - 1)));
  }
  else
  {
    throw IncorrectUsageException("Can only get element sort from array sort");
  }
}

string Yices2Sort::get_uninterpreted_name() const
{
  throw NotImplementedException(
      "get_uninterpreted_name not implemented for Yices2Sort");
}

size_t Yices2Sort::get_arity() const
{
  // yices2 does not support uninterpreted sorts with non-zero arity
  return 0;
}

SortVec Yices2Sort::get_uninterpreted_param_sorts() const
{
  throw NotImplementedException(
      "Yices2 does not support uninterpreted sort constructors");
}

Datatype Yices2Sort::get_datatype() const
{
  throw NotImplementedException("get_datatype");
};

bool Yices2Sort::compare(const Sort & s) const
{
  shared_ptr<Yices2Sort> ys = std::static_pointer_cast<Yices2Sort>(s);
  return type == ys->type;
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
  else
  {
    std::string msg("Unknown Yices2 type: ");
    msg += yices_type_to_string(type, 120, 1, 0);
    throw NotImplementedException(msg.c_str());
  }
}

}  // namespace smt
