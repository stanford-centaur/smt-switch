/*********************                                                        */
/*! \file sort_inference.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Utility functions for checking sortedness and computing the
**        expected sort when building a term.
**
**/

#include <algorithm>
#include <functional>
#include "assert.h"

#include "exceptions.h"
#include "sort_inference.h"

using namespace std;

namespace smt {

// a map used to look up the sortedness check in check_sortedness
const std::unordered_map<PrimOp, std::function<bool(const SortVec & sorts)>>
    sort_check_dispatch({ { And, bool_sorts },
                          { Or, bool_sorts },
                          { Xor, bool_sorts },
                          { Not, bool_sorts },
                          { Implies, bool_sorts },
                          { Iff, bool_sorts },
                          { Ite, check_ite_sorts },
                          { Equal, bool_sorts },
                          { Distinct, bool_sorts },
                          { Apply, check_apply_sorts },
                          { Plus, arithmetic_sorts },
                          { Minus, arithmetic_sorts },
                          { Negate, arithmetic_sorts },
                          { Mult, arithmetic_sorts },
                          { Div, arithmetic_sorts },
                          { Lt, bool_sorts },
                          { Le, bool_sorts },
                          { Gt, bool_sorts },
                          { Ge, bool_sorts },
                          { Mod, int_sorts },
                          // technically Abs/Pow only defined for integers in
                          // SMT-LIB but not sure if that's true for all solvers
                          // might also be good to be forward looking
                          { Abs, arithmetic_sorts },
                          { Pow, arithmetic_sorts },
                          { IntDiv, int_sorts },
                          { To_Real, int_sorts },
                          { To_Int, real_sorts },
                          { Is_Int, int_sorts },
                          { Concat, bv_sorts },
                          { Extract, bv_sorts },
                          { BVNot, bv_sorts },
                          { BVNeg, bv_sorts },
                          { BVAnd, bv_sorts },
                          { BVOr, bv_sorts },
                          { BVXor, bv_sorts },
                          { BVNand, bv_sorts },
                          { BVNor, bv_sorts },
                          { BVXnor, bv_sorts },
                          { BVAdd, bv_sorts },
                          { BVSub, bv_sorts },
                          { BVMul, bv_sorts },
                          { BVUdiv, bv_sorts },
                          { BVSdiv, bv_sorts },
                          { BVUrem, bv_sorts },
                          { BVSrem, bv_sorts },
                          { BVSmod, bv_sorts },
                          { BVShl, bv_sorts },
                          { BVAshr, bv_sorts },
                          { BVLshr, bv_sorts },
                          { BVComp, bv_sorts },
                          { BVUlt, bv_sorts },
                          { BVUle, bv_sorts },
                          { BVUgt, bv_sorts },
                          { BVUge, bv_sorts },
                          { BVSlt, bv_sorts },
                          { BVSle, bv_sorts },
                          { BVSgt, bv_sorts },
                          { BVSge, bv_sorts },
                          { Zero_Extend, bv_sorts },
                          { Sign_Extend, bv_sorts },
                          { Repeat, bv_sorts },
                          { Rotate_Left, bv_sorts },
                          { Rotate_Right, bv_sorts },
                          { BV_To_Nat, bv_sorts },
                          { Int_To_BV, int_sorts },
                          { Select, check_select_sorts },
                          { Store, check_store_sorts }

    });

// main function implementations
bool check_sortedness(Op op, const TermVec & terms)
{
  if (sort_check_dispatch.find(op.prim_op) != sort_check_dispatch.end())
  {
    SortVec sorts;
    sorts.reserve(terms.size());
    for (auto t : terms)
    {
      sorts.push_back(t->get_sort());
    }
    return sort_check_dispatch.at(op.prim_op)(sorts);
  }
  else
  {
    throw NotImplementedException("Sort checking for operator " + op.to_string()
                                  + " is not yet implemented.");
  }
}

// helper function implementations
bool equal_sorts(const SortVec & sorts)
{
  assert(sorts.size());
  return (adjacent_find(sorts.begin(), sorts.end(), not_equal_to<Sort>())
          == sorts.end());
}

bool equal_sortkinds(const SortVec & sorts)
{
  assert(sorts.size());
  SortKind first_sk = sorts[0]->get_sort_kind();
  for (auto it = next(sorts.begin()); it != sorts.end(); ++it)
  {
    if (first_sk != (*it)->get_sort_kind())
    {
      return false;
    }
  }
  return true;
}

bool check_ite_sorts(const SortVec & sorts)
{
  assert(sorts.size() == 3);
  return sorts[0]->get_sort_kind() == BOOL && sorts[1] == sorts[2];
}

bool check_sortkind_matches(SortKind sk, const SortVec & sorts)
{
  for (auto sort : sorts)
  {
    if (sk != sort->get_sort_kind())
    {
      return false;
    }
  }
  return true;
}

bool check_apply_sorts(const SortVec & sorts)
{
  assert(sorts.size());
  Sort funsort = sorts[0];
  if (funsort->get_sort_kind() != FUNCTION)
  {
    return false;
  }

  SortVec domain_sorts = funsort->get_domain_sorts();
  if (domain_sorts.size() != sorts.size() + 1)
  {
    // expecting same number of arguments to function as arity
    return false;
  }

  for (size_t i = 0; i < domain_sorts.size(); ++i)
  {
    if (domain_sorts[i] != sorts[i + 1])
    {
      return false;
    }
  }
  return true;
}

bool check_select_sorts(const SortVec & sorts)
{
  assert(sorts.size());
  if (sorts.size() != 2)
  {
    return false;
  }

  Sort arrsort = sorts[0];
  if (arrsort->get_sort_kind() != ARRAY)
  {
    return false;
  }

  if (sorts[1] != arrsort->get_indexsort())
  {
    return false;
  }

  return true;
}

bool check_store_sorts(const SortVec & sorts)
{
  assert(sorts.size());
  if (sorts.size() != 3)
  {
    return false;
  }

  Sort arrsort = sorts[0];
  if (arrsort->get_sort_kind() != ARRAY)
  {
    return false;
  }

  if (sorts[1] != arrsort->get_indexsort())
  {
    return false;
  }
  else if (sorts[2] != arrsort->get_elemsort())
  {
    return false;
  }

  return true;
}

}  // namespace smt
