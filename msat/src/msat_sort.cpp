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

#include "exceptions.h"

using namespace std;

namespace smt {

// MsatSort implementation

std::size_t MsatSort::hash() const
{
  // TODO: check this hash function
  // mathsat doesn't hash types
  // so we need to generate a type
  std::size_t v = 1;

  // giving lower 20 bits for representing a width if it's a bit-vector
  size_t out_width;
  msat_type idx_type;
  msat_type elem_type;

  if (msat_is_integer_type(env, type))
  {
    v = v << 20;
  }
  else if (msat_is_rational_type(env, type))
  {
    v = v << 21;
  }
  else if (msat_is_bool_type(env, type))
  {
    v = v << 22;
  }
  else if (msat_is_bv_type(env, type, &out_width))
  {
    v = v << 23;
    v = v ^ out_width;
  }
  else if (msat_is_array_type(env, type, &idx_type, &elem_type))
  {
    v = v << 24;
    v = v ^ MsatSort(env, idx_type).hash();
    v = v ^ MsatSort(env, elem_type).hash();
  }
  else if (is_uf_type)
  {
    v = v << 25;
    for (auto t : get_domain_sorts())
    {
      v = v ^ t->hash();
    }
    v = v ^ get_codomain_sort()->hash();
  }
  else
  {
    throw NotImplementedException("Unknown MathSAT type.");
  }

  return v;
}

uint64_t MsatSort::get_width() const
{
  size_t out_width;
  if (msat_is_bv_type(env, type, &out_width))
  {
    // TODO: figure out if this is safe -- only for large bit-widths is this a
    // problem
    return (unsigned int)out_width;
  }
  else
  {
    throw IncorrectUsageException("Can only get width from bit-vector sort");
  }
}

Sort MsatSort::get_indexsort() const
{
  msat_type idx_type;
  if (msat_is_array_type(env, type, &idx_type, nullptr))
  {
    return std::make_shared<MsatSort> (env, idx_type);
  }
  else
  {
    throw IncorrectUsageException("Can only get index sort from array sort");
  }
}

Sort MsatSort::get_elemsort() const
{
  msat_type elem_type;
  if (msat_is_array_type(env, type, nullptr, &elem_type))
  {
    return std::make_shared<MsatSort> (env, elem_type);
  }
  else
  {
    throw IncorrectUsageException("Can only get index sort from array sort");
  }
}

SortVec MsatSort::get_domain_sorts() const
{
  if (!is_uf_type)
  {
    throw IncorrectUsageException("Can't get domain sorts from non-function sort.");
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
    sorts.push_back(std::make_shared<MsatSort> (env, tmp_type));
  }
  return sorts;
}

Sort MsatSort::get_codomain_sort() const
{
  if (!is_uf_type)
  {
    throw IncorrectUsageException("Can't get codomain sort from non-function sort.");
  }
  msat_type t = msat_decl_get_return_type(uf_decl);
  // Note: assuming first-order, e.g. functions can't return functions
  if (MSAT_ERROR_TYPE(t))
  {
    throw InternalSolverException("Got error type");
  }
  return std::make_shared<MsatSort> (env, t);
}

string MsatSort::get_uninterpreted_name() const
{
  string res(msat_type_repr(type));
  return res;
}

bool MsatSort::compare(const Sort s) const
{
  std::shared_ptr<MsatSort> msort = std::static_pointer_cast<MsatSort>(s);
  return msat_type_equals(type, msort->type);
}

SortKind MsatSort::get_sort_kind() const
{
  if (msat_is_integer_type(env, type))
  {
    return INT;
  }
  else if (msat_is_rational_type(env, type))
  {
    return REAL;
  }
  else if (msat_is_bool_type(env, type))
  {
    return BOOL;
  }
  else if (msat_is_bv_type(env, type, nullptr))
  {
    return BV;
  }
  else if (msat_is_array_type(env, type, nullptr, nullptr))
  {
    return ARRAY;
  }
  else if (is_uf_type)
  {
    return FUNCTION;
  }
  else if (msat_is_fp_type(env, type, nullptr, nullptr))
  {
    throw NotImplementedException(
        "Floating point not implemented for MathSAT yet.");
  }
  else if (msat_is_fp_roundingmode_type(env, type))
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
