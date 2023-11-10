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

#include "exceptions.h"
#include "sort_inference.h"

using namespace std;

namespace smt {

// a map used to look up the sortedness check functions in check_sortedness
// maps primitive operators to a function used to check that the sorts are
// expected
const std::unordered_map<PrimOp, std::function<bool(const SortVec & sorts)>>
    sort_check_dispatch({ { And, bool_sorts },
                          { Or, bool_sorts },
                          { Xor, bool_sorts },
                          { Not, bool_sorts },
                          { Implies, bool_sorts },
                          { Ite, check_ite_sorts },
                          { Equal, arith_equal_sorts },
                          { Distinct, arith_equal_sorts },
                          { Apply, check_apply_sorts },
                          { Plus, arithmetic_sorts },
                          { Minus, arithmetic_sorts },
                          { Negate, arithmetic_sorts },
                          { Mult, arithmetic_sorts },
                          { Div, arithmetic_sorts },
                          { Lt, arithmetic_sorts },
                          { Le, arithmetic_sorts },
                          { Gt, arithmetic_sorts },
                          { Ge, arithmetic_sorts },
                          { Mod, int_sorts },
                          // technically Abs/Pow only defined for integers in
                          // SMT-LIB but not sure if that's true for all solvers
                          // might also be good to be forward looking
                          { Abs, int_sorts },
                          { Pow, int_sorts },
                          { IntDiv, int_sorts },
                          { To_Real, int_sorts },
                          { To_Int, real_sorts },
                          { Is_Int, int_sorts },
                          { Concat, bv_sorts },
                          { Extract, bv_sorts },
                          { BVNot, bv_sorts },
                          { BVNeg, bv_sorts },
                          { BVAnd, eq_bv_sorts },
                          { BVOr, eq_bv_sorts },
                          { BVXor, eq_bv_sorts },
                          { BVNand, eq_bv_sorts },
                          { BVNor, eq_bv_sorts },
                          { BVXnor, eq_bv_sorts },
                          { BVAdd, eq_bv_sorts },
                          { BVSub, eq_bv_sorts },
                          { BVMul, eq_bv_sorts },
                          { BVUdiv, eq_bv_sorts },
                          { BVSdiv, eq_bv_sorts },
                          { BVUrem, eq_bv_sorts },
                          { BVSrem, eq_bv_sorts },
                          { BVSmod, eq_bv_sorts },
                          { BVShl, eq_bv_sorts },
                          { BVAshr, eq_bv_sorts },
                          { BVLshr, eq_bv_sorts },
                          { BVComp, eq_bv_sorts },
                          { BVUlt, eq_bv_sorts },
                          { BVUle, eq_bv_sorts },
                          { BVUgt, eq_bv_sorts },
                          { BVUge, eq_bv_sorts },
                          { BVSlt, eq_bv_sorts },
                          { BVSle, eq_bv_sorts },
                          { BVSgt, eq_bv_sorts },
                          { BVSge, eq_bv_sorts },
                          { Zero_Extend, bv_sorts },
                          { Sign_Extend, bv_sorts },
                          { Repeat, bv_sorts },
                          { Rotate_Left, bv_sorts },
                          { Rotate_Right, bv_sorts },
                          { BV_To_Nat, bv_sorts },
                          { Int_To_BV, int_sorts },
                          { StrLt, string_sorts },
                          { StrLeq, string_sorts },
                          { StrConcat, string_sorts },
                          { StrLen, string_sorts },
                          { StrSubstr, check_substr_sorts },
                          { StrAt, check_charat_sorts },
                          { StrContains, string_sorts },
                          { StrIndexof, check_indexof_sorts },
                          { StrReplace, string_sorts },
                          { StrReplaceAll, string_sorts },
                          { StrPrefixof, string_sorts },
                          { StrSuffixof, string_sorts },
                          { StrIsDigit, string_sorts },
                          { Select, check_select_sorts },
                          { Store, check_store_sorts },
                          { Forall, check_quantifier_sorts },
                          { Exists, check_quantifier_sorts },
                          { Apply_Constructor, check_constructor_sorts },
                          { Apply_Selector, check_selector_sorts },
                          { Apply_Tester, check_tester_sorts }

    });

// map from Primitive Operators to the corresponding sort inference function
// used in compute_sort
const std::unordered_map<
    PrimOp,
    std::function<
        Sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)>>
    sort_comp_dispatch({
        { And, bool_sort },
        { Or, bool_sort },
        { Xor, bool_sort },
        { Not, bool_sort },
        { Implies, bool_sort },
        { Ite, ite_sort },
        { Equal, bool_sort },
        { Distinct, bool_sort },
        { Apply, apply_sort },
        { Plus, same_sort },
        { Minus, same_sort },
        { Negate, same_sort },
        { Mult, same_sort },
        { Div, same_sort },
        { Lt, bool_sort },
        { Le, bool_sort },
        { Gt, bool_sort },
        { Ge, bool_sort },
        { Mod, int_sort },
        // technically Abs/Pow only defined for integers in
        // SMT-LIB but not sure if that's true for all solvers
        // might also be good to be forward looking
        { Abs, same_sort },
        { Pow, same_sort },
        { IntDiv, int_sort },
        { To_Real, real_sort },
        { To_Int, int_sort },
        { Is_Int, bool_sort },
        { Concat, concat_sort },
        { Extract, extract_sort },
        { BVNot, same_sort },
        { BVNeg, same_sort },
        { BVAnd, same_sort },
        { BVOr, same_sort },
        { BVXor, same_sort },
        { BVNand, same_sort },
        { BVNor, same_sort },
        { BVXnor, same_sort },
        { BVAdd, same_sort },
        { BVSub, same_sort },
        { BVMul, same_sort },
        { BVUdiv, same_sort },
        { BVSdiv, same_sort },
        { BVUrem, same_sort },
        { BVSrem, same_sort },
        { BVSmod, same_sort },
        { BVShl, same_sort },
        { BVAshr, same_sort },
        { BVLshr, same_sort },
        { BVComp, single_bit_sort },
        { BVUlt, bool_sort },
        { BVUle, bool_sort },
        { BVUgt, bool_sort },
        { BVUge, bool_sort },
        { BVSlt, bool_sort },
        { BVSle, bool_sort },
        { BVSgt, bool_sort },
        { BVSge, bool_sort },
        { Zero_Extend, extend_sort },
        { Sign_Extend, extend_sort },
        { Repeat, repeat_sort },
        { Rotate_Left, same_sort },
        { Rotate_Right, same_sort },
        { BV_To_Nat, int_sort },
        { Int_To_BV, int_to_bv_sort },
        { StrLt, bool_sort },
        { StrLeq, bool_sort },
        { StrConcat, string_sort },
        { StrLen, int_sort },
        { StrSubstr, string_sort },
        { StrAt, string_sort },
        { StrContains, bool_sort },
        { StrIndexof, int_sort },
        { StrReplace, string_sort },
        { StrReplaceAll, string_sort },
        { StrPrefixof, bool_sort },
        { StrSuffixof, bool_sort },
        { StrIsDigit, bool_sort },
        { Select, select_sort },
        { Store, store_sort },
        { Forall, bool_sort },
        { Exists, bool_sort },
        { Apply_Constructor, constructor_sort },
        { Apply_Tester, bool_sort },
        { Apply_Selector, selector_sort },
    });

// main function implementations
bool check_sortedness(Op op, const TermVec & terms)
{
  PrimOp po = op.prim_op;
  if (po == Forall || po == Exists)
  {
    // special-case check terms for quantified ops
    // will check that first term is a parameter
    // this info is not available over sorts
    return check_quantifier_terms(terms);
  }

  SortVec sorts;
  sorts.reserve(terms.size());
  for (auto t : terms)
  {
    sorts.push_back(t->get_sort());
  }
  return check_sortedness(op, sorts);
}

bool check_sortedness(Op op, const SortVec & sorts)
{
  auto min_max_arity = get_arity(op.prim_op);
  size_t num_args = sorts.size();
  if (num_args < min_max_arity.first || num_args > min_max_arity.second)
  {
    // wrong number of arguments
    return false;
  }

  if (sort_check_dispatch.find(op.prim_op) != sort_check_dispatch.end())
  {
    return sort_check_dispatch.at(op.prim_op)(sorts);
  }
  else
  {
    throw NotImplementedException("Sort checking for operator " + op.to_string()
                                  + " is not yet implemented.");
  }
}

Sort compute_sort(Op op, const AbsSmtSolver * solver, const TermVec & terms)
{
  assert(terms.size());
  SortVec sorts;
  for (auto t : terms)
  {
    sorts.push_back(t->get_sort());
  }
  return sort_comp_dispatch.at(op.prim_op)(op, solver, sorts);
}

Sort compute_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  assert(sorts.size());
  return sort_comp_dispatch.at(op.prim_op)(op, solver, sorts);
}

Sort compute_sort(Op op, const SmtSolver solver, const TermVec & terms)
{
  return compute_sort(op, solver.get(), terms);
}

Sort compute_sort(Op op, const SmtSolver solver, const SortVec & sorts)
{
  return compute_sort(op, solver.get(), sorts);
}

// helper function implementations

bool check_quantifier_terms(const TermVec & terms)
{
  return terms.size() == 2 &&
    terms[0]->is_param() &&
    terms[1]->get_sort()->get_sort_kind() == BOOL;
}

/* helpers for sort checking */

bool check_quantifier_sorts(const SortVec & sorts)
{
  return sorts.size() == 2 &&
    sorts[1]->get_sort_kind() == BOOL;
}

bool equal_sorts(const SortVec & sorts)
{
  assert(sorts.size());
  return (adjacent_find(sorts.begin(), sorts.end(), not_equal_to<Sort>())
          == sorts.end());
}

bool arith_equal_sorts(const SortVec & sorts)
{
  return equal_sorts(sorts) || arithmetic_sorts(sorts);
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

bool check_one_of_sortkinds(const unordered_set<SortKind> & sks,
                            const SortVec & sorts)
{
  for (auto sort : sorts)
  {
    if (sks.find(sort->get_sort_kind()) == sks.end())
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
  if (domain_sorts.size() + 1 != sorts.size())
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

bool check_selector_sorts(const SortVec & sorts)
{
  assert(sorts.size());
  if (sorts.size() != 1)
  {
    return false;
  }

  Sort dt_sort = sorts[0];
  return dt_sort->get_sort_kind() == DATATYPE;
}
// TO DO!!! DO THIS LATER
bool check_constructor_sorts(const SortVec & sorts)
{
  assert(sorts.size());
  if (sorts.size() != 1)
  {
    return false;
  }
  Sort dt_sort = sorts[0];
  return dt_sort->get_sort_kind() == DATATYPE;
}

// TO DO!!! DO THIS LATER
bool check_tester_sorts(const SortVec & sorts)
{
  assert(sorts.size());
  if (sorts.size() != 1)
  {
    return false;
  }
  Sort dt_sort = sorts[0];
  return dt_sort->get_sort_kind() == BOOL;
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

bool check_substr_sorts(const SortVec & sorts)
{
  assert(sorts.size());
  if (sorts.size() != 3)
  {
    return false;
  }

  Sort strsort = sorts[0];
  if (strsort->get_sort_kind() != STRING)
  {
    return false;
  }

  if (sorts[1]->get_sort_kind() != INT)
  {
    return false;
  }
  else if (sorts[2]->get_sort_kind() != INT)
  {
    return false;
  }

  return true;
}

bool check_charat_sorts(const SortVec & sorts)
{
  assert(sorts.size());
  if (sorts.size() != 2)
  {
    return false;
  }

  Sort strsort = sorts[0];
  if (strsort->get_sort_kind() != STRING)
  {
    return false;
  }

  if (sorts[1]->get_sort_kind() != INT)
  {
    return false;
  }
  
  return true;
}

bool check_indexof_sorts(const SortVec & sorts)
{
  assert(sorts.size());
  if (sorts.size() != 3)
  {
    return false;
  }

  Sort strsort = sorts[0];
  if (strsort->get_sort_kind() != STRING)
  {
    return false;
  }

  if (sorts[1]->get_sort_kind() != STRING)
  {
    return false;
  }
  else if (sorts[2]->get_sort_kind() != INT)
  {
    return false;
  }

  return true;
}

bool bool_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(BOOL, sorts);
};

bool bv_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(BV, sorts);
};

bool eq_bv_sorts(const SortVec & sorts)
{
  assert(sorts.size());
  return sorts[0]->get_sort_kind() == BV && equal_sorts(sorts);
};

bool real_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(REAL, sorts);
};

bool int_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(INT, sorts);
};

bool string_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(STRING, sorts);
};

bool arithmetic_sorts(const SortVec & sorts)
{
  return check_one_of_sortkinds({ INT, REAL }, sorts);
}

bool array_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(ARRAY, sorts);
};

bool function_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(FUNCTION, sorts);
};

/* helpers for sort inference (return type of operation) */

/* Common sort computation helper functions */

Sort same_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  return sorts[0];
}

Sort bool_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  return solver->make_sort(BOOL);
}

Sort single_bit_sort(Op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  return solver->make_sort(BV, 1);
}

Sort real_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  return solver->make_sort(REAL);
}

Sort int_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  return solver->make_sort(INT);
}

Sort string_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  return solver->make_sort(STRING);
}


Sort ite_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  if (sorts[1] != sorts[2])
  {
    throw IncorrectUsageException("Ite element sorts don't match: "
                                  + sorts[1]->to_string() + ", "
                                  + sorts[2]->to_string());
  }
  return sorts[1];
}

Sort extract_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  return solver->make_sort(BV, op.idx0 - op.idx1 + 1);
}

Sort concat_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  return solver->make_sort(BV, sorts[0]->get_width() + sorts[1]->get_width());
}

Sort extend_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  return solver->make_sort(BV, op.idx0 + sorts[0]->get_width());
}

Sort repeat_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  return solver->make_sort(BV, op.idx0 * sorts[0]->get_width());
}

Sort int_to_bv_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  return solver->make_sort(BV, op.idx0);
}

Sort apply_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  Sort funsort = sorts[0];
  if (funsort->get_sort_kind() != FUNCTION)
  {
    throw IncorrectUsageException(
        "Expecting first argument to Apply to be a function but got "
        + funsort->to_string());
  }
  return funsort->get_codomain_sort();
}

Sort select_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  Sort arraysort = sorts[0];
  if (arraysort->get_sort_kind() != ARRAY)
  {
    throw IncorrectUsageException(
        "Expecting first argument of Select to be an array but got: "
        + arraysort->to_string());
  }
  return arraysort->get_elemsort();
}

Sort store_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  Sort arraysort = sorts[0];
  if (arraysort->get_sort_kind() != ARRAY)
  {
    throw IncorrectUsageException(
        "Expecting first argument of Store to be an array but got: "
        + arraysort->to_string());
  }
  return arraysort;
}

Sort selector_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  Sort parent_sort = (sorts[0])->get_domain_sorts()[0];
  return static_pointer_cast<DatatypeComponentSort>(sorts[0])
      ->get_codomain_sort();
}
Sort constructor_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  return (sorts[0])->get_codomain_sort();
}
Sort tester_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  return solver->make_sort(BOOL);
}

}  // namespace smt
