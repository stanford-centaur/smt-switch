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

#include <gmp.h>  // IWYU pragma: keep (required by yices.h)
#include <yices.h>

#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <vector>

#include "exceptions.h"
#include "yices2_extensions.h"

namespace smt {

// Yices2Sort implementation

Yices2Sort::Yices2Sort(type_t y_type, bool is_fun, std::int32_t constructor)
    : type(y_type), is_function(is_fun), constructor_id(constructor)
{
}

std::size_t Yices2Sort::hash() const
{
  // type_t is a unique id, see Yices2 docs, and so is a constructor's macro
  // id, which a constructor has in place of a type
  return constructor_id < 0 ? std::hash<type_t>{}(type)
                            : ~std::hash<std::int32_t>{}(constructor_id);
}

std::uint64_t Yices2Sort::get_width() const
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
  std::int32_t s_arity = yices_type_num_children(type) - 1;
  SortVec sorts;
  sorts.reserve(s_arity);

  for (std::int32_t i = 0; i < s_arity; i++)
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

std::string Yices2Sort::get_uninterpreted_name() const
{
  SortKind sk = get_sort_kind();
  if (sk == UNINTERPRETED_CONS)
  {
    return Yices2InstanceRef::get_constructor_name(constructor_id);
  }
  if (sk == UNINTERPRETED)
  {
    // an applied sort is named after its constructor
    std::int32_t applied = Yices2InstanceRef::get_instance_constructor(type);
    if (applied >= 0)
    {
      return Yices2InstanceRef::get_constructor_name(applied);
    }
    const char * res = yices_get_type_name(type);
    if (res == NULL)
    {
      throw InternalSolverException(
          "Failed to get the name of an uninterpreted sort");
    }
    return res;
  }
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no uninterpreted name");
}

std::size_t Yices2Sort::get_arity() const
{
  SortKind sk = get_sort_kind();
  if (sk == UNINTERPRETED_CONS)
  {
    return Yices2InstanceRef::get_constructor_arity(constructor_id);
  }
  if (sk == UNINTERPRETED)
  {
    return 0;
  }
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no arity");
}

Sort Yices2Sort::get_uninterpreted_constructor() const
{
  std::int32_t id = Yices2InstanceRef::get_instance_constructor(type);
  if (id < 0)
  {
    throw IncorrectUsageException("Sort " + to_string()
                                  + " was not made by applying a sort "
                                    "constructor");
  }
  return std::make_shared<Yices2Sort>(NULL_TYPE, false, id);
}

SortVec Yices2Sort::get_uninterpreted_param_sorts() const
{
  if (get_sort_kind() != UNINTERPRETED)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no uninterpreted param sorts");
  }
  if (Yices2InstanceRef::get_instance_constructor(type) < 0)
  {
    return {};
  }
  SortVec params;
  for (type_t p : Yices2InstanceRef::get_instance_params(type))
  {
    params.push_back(std::make_shared<Yices2Sort>(p));
  }
  return params;
}

Datatype Yices2Sort::get_datatype() const
{
  // Yices2 has no datatypes, so no sort has a datatype
  throw IncorrectUsageException(
      "Sort of kind " + smt::to_string(get_sort_kind()) + " has no datatype");
}

bool Yices2Sort::compare(const Sort & s) const
{
  std::shared_ptr<Yices2Sort> ys = std::dynamic_pointer_cast<Yices2Sort>(s);
  return ys && type == ys->type && constructor_id == ys->constructor_id;
}

SortKind Yices2Sort::get_sort_kind() const
{
  if (constructor_id >= 0)
  {
    return UNINTERPRETED_CONS;
  }
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
  else if (yices_type_is_uninterpreted(type)
           || Yices2InstanceRef::get_instance_constructor(type) >= 0)
  {
    // Yices does not count an applied sort constructor as an uninterpreted
    // type; only the record knows it is one
    return UNINTERPRETED;
  }
  else
  {
    std::string msg("smt-switch has no SortKind for the Yices2 sort ");
    msg += detail::get_yices2_string(yices_type_to_string(type, 120, 1, 0));
    throw NotImplementedException(msg.c_str());
  }
}

type_t Yices2Sort::get_ytype() const
{
  if (constructor_id >= 0)
  {
    throw IncorrectUsageException("Sort constructor " + get_uninterpreted_name()
                                  + " is not a term sort until it is applied");
  }
  return type;
}

}  // namespace smt
