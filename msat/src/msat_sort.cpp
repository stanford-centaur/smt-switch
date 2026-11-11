/*********************                                                        */
/*! \file msat_sort.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief MathSAT implementation of AbsSort
**
**
**/

#include "msat_sort.h"

#include <mathsat.h>

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <utility>

#include "exceptions.h"
#include "utils.h"

namespace smt {

// MsatSort implementation

MsatSort::MsatSort(const std::shared_ptr<MsatEnv> & e, msat_type t)
    : env(e), type(t)
{
}

MsatSort::MsatSort(const std::shared_ptr<MsatEnv> & e,
                   std::string name,
                   std::uint64_t arity)
    : env(e),
      type(),
      is_constructor(true),
      constructor_name(std::move(name)),
      constructor_arity(arity)
{
}

std::size_t MsatSort::hash() const
{
  // MathSAT numbers types per environment, and msat_type_equals tells
  // environments apart, so mix in the environment
  std::size_t h = std::hash<MsatEnv *>{}(env.get());
  if (is_constructor)
  {
    detail::hash_combine(h, std::hash<std::string>{}(constructor_name));
    detail::hash_combine(h, constructor_arity);
  }
  else
  {
    detail::hash_combine(h, msat_type_id(type));
  }
  return h;
}

std::uint64_t MsatSort::get_width() const
{
  std::size_t out_width;
  if (is_constructor || !msat_is_bv_type(*env, type, &out_width))
  {
    throw IncorrectUsageException(
        "Sort of kind " + smt::to_string(get_sort_kind()) + " has no width");
  }
  return out_width;
}

Sort MsatSort::get_indexsort() const
{
  msat_type idx_type;
  if (is_constructor || !msat_is_array_type(*env, type, &idx_type, nullptr))
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no index sort");
  }
  return std::make_shared<MsatSort>(env, idx_type);
}

Sort MsatSort::get_elemsort() const
{
  msat_type elem_type;
  if (is_constructor || !msat_is_array_type(*env, type, nullptr, &elem_type))
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no element sort");
  }
  return std::make_shared<MsatSort>(env, elem_type);
}

SortVec MsatSort::get_domain_sorts() const
{
  std::size_t arity;
  msat_type * param_types;
  if (is_constructor
      || !msat_is_function_type(*env, type, &arity, &param_types, nullptr))
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no domain sorts");
  }
  SortVec sorts;
  sorts.reserve(arity);
  for (std::size_t i = 0; i < arity; i++)
  {
    sorts.push_back(std::make_shared<MsatSort>(env, param_types[i]));
  }
  msat_free(param_types);
  return sorts;
}

Sort MsatSort::get_codomain_sort() const
{
  msat_type return_type;
  if (is_constructor
      || !msat_is_function_type(*env, type, nullptr, nullptr, &return_type))
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no codomain sort");
  }
  return std::make_shared<MsatSort>(env, return_type);
}

std::string MsatSort::get_uninterpreted_name() const
{
  SortKind sk = get_sort_kind();
  if (sk == UNINTERPRETED_CONS)
  {
    return constructor_name;
  }
  if (sk == UNINTERPRETED)
  {
    // an applied sort is named after its constructor, not its MathSAT type
    return env->get_instance_name(type);
  }
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no uninterpreted name");
}

std::size_t MsatSort::get_arity() const
{
  SortKind sk = get_sort_kind();
  if (sk == UNINTERPRETED_CONS)
  {
    return constructor_arity;
  }
  if (sk == UNINTERPRETED)
  {
    return 0;
  }
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no arity");
}

Sort MsatSort::get_uninterpreted_constructor() const
{
  if (get_sort_kind() != UNINTERPRETED || !env->is_instance(type))
  {
    throw IncorrectUsageException("Sort " + to_string()
                                  + " was not made by applying a sort "
                                    "constructor");
  }
  // MathSAT gives the same type back for the same name, so a constructor is
  // its name and arity
  return std::make_shared<MsatSort>(
      env, env->get_instance_name(type), env->get_instance_params(type).size());
}

SortVec MsatSort::get_uninterpreted_param_sorts() const
{
  if (get_sort_kind() != UNINTERPRETED)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no uninterpreted param sorts");
  }
  auto msat_params = env->get_instance_params(type);
  SortVec params;
  params.reserve(msat_params.size());
  for (msat_type p : msat_params)
  {
    params.push_back(std::make_shared<MsatSort>(env, p));
  }
  return params;
}

Datatype MsatSort::get_datatype() const
{
  // MathSAT has no datatypes, so no sort has a datatype
  throw IncorrectUsageException(
      "Sort of kind " + smt::to_string(get_sort_kind()) + " has no datatype");
}

bool MsatSort::compare(const Sort & s) const
{
  std::shared_ptr<MsatSort> msort = std::dynamic_pointer_cast<MsatSort>(s);
  if (!msort || is_constructor != msort->is_constructor)
  {
    return false;
  }
  if (is_constructor)
  {
    // MathSAT gives the same type back for the same name, so constructors
    // of the same name and arity are the same constructor
    return env == msort->env && constructor_name == msort->constructor_name
           && constructor_arity == msort->constructor_arity;
  }
  return msat_type_equals(type, msort->type);
}

SortKind MsatSort::get_sort_kind() const
{
  if (is_constructor)
  {
    return UNINTERPRETED_CONS;
  }
  if (msat_is_integer_type(*env, type))
  {
    return INT;
  }
  else if (msat_is_rational_type(*env, type))
  {
    return REAL;
  }
  else if (msat_is_bool_type(*env, type))
  {
    return BOOL;
  }
  else if (msat_is_bv_type(*env, type, nullptr))
  {
    return BV;
  }
  else if (msat_is_array_type(*env, type, nullptr, nullptr))
  {
    return ARRAY;
  }
  else if (msat_is_function_type(*env, type, nullptr, nullptr, nullptr))
  {
    return FUNCTION;
  }
  else if (msat_is_fp_type(*env, type, nullptr, nullptr))
  {
    throw NotImplementedException(
        "Floating point not implemented for MathSAT yet.");
  }
  else if (msat_is_fp_roundingmode_type(*env, type))
  {
    throw NotImplementedException(
        "Floating point not implemented for MathSAT yet.");
  }
  else
  {
    // no way to test if type is a simple type
    // just process of elimination
    return UNINTERPRETED;
  }
}

msat_type MsatSort::get_msat_type() const
{
  if (is_constructor)
  {
    throw IncorrectUsageException("Sort constructor " + constructor_name
                                  + " is not a term sort until it is applied");
  }
  return type;
}

}  // namespace smt
