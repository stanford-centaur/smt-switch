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

#include <cstdint>

#include "exceptions.h"

using namespace std;

namespace smt {

// MsatSort implementation

MsatSort::MsatSort(const std::shared_ptr<msat_env> & e, msat_type t)
    : env(e), type(t)
{
}

MsatSort::MsatSort(const std::shared_ptr<msat_env> & e,
                   msat_type t,
                   msat_decl d)
    : env(e), type(t), uf_decl(d), is_uf_type(true)
{
}

std::size_t MsatSort::hash() const
{
  // unique within the type's environment, as msat_type_equals is
  return msat_type_id(type);
}

uint64_t MsatSort::get_width() const
{
  size_t out_width;
  if (!msat_is_bv_type(*env, type, &out_width))
  {
    throw IncorrectUsageException(
        "Sort of kind " + smt::to_string(get_sort_kind()) + " has no width");
  }
  // TODO: figure out if this is safe -- only for large bit-widths is this a
  // problem
  return (unsigned int)out_width;
}

Sort MsatSort::get_indexsort() const
{
  msat_type idx_type;
  if (!msat_is_array_type(*env, type, &idx_type, nullptr))
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
  if (!msat_is_array_type(*env, type, nullptr, &elem_type))
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no element sort");
  }
  return std::make_shared<MsatSort>(env, elem_type);
}

SortVec MsatSort::get_domain_sorts() const
{
  if (!is_uf_type)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no domain sorts");
  }

  size_t arity = msat_decl_get_arity(uf_decl);
  SortVec sorts;
  sorts.reserve(arity);
  msat_type tmp_type;
  for (size_t i = 0; i < arity; i++)
  {
    tmp_type = msat_decl_get_arg_type(uf_decl, i);
    if (MSAT_ERROR_TYPE(type))
    {
      throw InternalSolverException("Got error type");
    }
    // Note: assuming first-order, function can't take function arguments
    sorts.push_back(std::make_shared<MsatSort>(env, tmp_type));
  }
  return sorts;
}

Sort MsatSort::get_codomain_sort() const
{
  if (!is_uf_type)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no codomain sort");
  }
  msat_type t = msat_decl_get_return_type(uf_decl);
  // Note: assuming first-order, e.g. functions can't return functions
  if (MSAT_ERROR_TYPE(t))
  {
    throw InternalSolverException("Got error type");
  }
  return std::make_shared<MsatSort>(env, t);
}

string MsatSort::get_uninterpreted_name() const
{
  if (get_sort_kind() != UNINTERPRETED)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no uninterpreted name");
  }
  string res(msat_type_repr(type));
  return res;
}

size_t MsatSort::get_arity() const
{
  if (get_sort_kind() != UNINTERPRETED)
  {
    throw IncorrectUsageException(
        "Sort of kind " + smt::to_string(get_sort_kind()) + " has no arity");
  }
  // MathSAT does not support uninterpreted sorts with non-zero arity
  return 0;
}

SortVec MsatSort::get_uninterpreted_param_sorts() const
{
  if (get_sort_kind() != UNINTERPRETED)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no uninterpreted param sorts");
  }
  // MathSAT has no sort constructors, so no sort has parameters
  return {};
}

Datatype MsatSort::get_datatype() const
{
  // MathSAT has no datatypes, so no sort has a datatype
  throw IncorrectUsageException(
      "Sort of kind " + smt::to_string(get_sort_kind()) + " has no datatype");
};

bool MsatSort::compare(const Sort & s) const
{
  std::shared_ptr<MsatSort> msort = std::dynamic_pointer_cast<MsatSort>(s);
  return msort && msat_type_equals(type, msort->type);
}

SortKind MsatSort::get_sort_kind() const
{
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
  else if (is_uf_type)
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

}  // namespace smt
