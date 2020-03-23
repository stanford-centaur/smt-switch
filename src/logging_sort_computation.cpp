#include "logging_sort_computation.h"
#include "exceptions.h"

#include <functional>
#include <unordered_map>

using namespace std;

namespace smt {

const std::unordered_map<PrimOp,
                         std::function<Sort(Op op, SortVec & sorts, Sort & w)>>
    sort_comp_dispatch({ { And, bool_sort },
                         { Or, bool_sort },
                         { Xor, bool_sort },
                         { Not, bool_sort },
                         { Implies, bool_sort },
                         { Iff, bool_sort },
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
                         { BVComp, bool_sort },
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
                         { Select, select_sort },
                         { Store, store_sort }

    });

Sort compute_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
{
  if (sorts.size() == 0)
  {
    throw SmtException("Zero sorts provided for sort computation");
  }

  return sort_comp_dispatch.at(op.prim_op)(op, sorts, wrapped_res_sort);
}

/* Common sort computation helper functions */

Sort same_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
{
  return sorts[0];
}

Sort bool_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
{
  Sort boolsort(new LoggingSort(BOOL, wrapped_res_sort));
  return boolsort;
}

Sort real_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
{
  Sort realsort(new LoggingSort(REAL, wrapped_res_sort));
  return realsort;
}

Sort int_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
{
  Sort intsort(new LoggingSort(INT, wrapped_res_sort));
  return intsort;
}

Sort ite_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
{
  if (sorts[1] != sorts[2])
  {
    throw IncorrectUsageException("Ite element sorts don't match: "
                                  + sorts[1]->to_string() + ", "
                                  + sorts[2]->to_string());
  }
  return sorts[1];
}

Sort extract_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
{
  Sort bvsort(new BVLoggingSort(wrapped_res_sort, op.idx0 - op.idx1 + 1));
  return bvsort;
}

Sort concat_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
{
  Sort bvsort(new BVLoggingSort(wrapped_res_sort,
                                sorts[0]->get_width() + sorts[1]->get_width()));
  return bvsort;
}

Sort extend_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
{
  Sort bvsort(
      new BVLoggingSort(wrapped_res_sort, op.idx0 + sorts[0]->get_width()));
  return bvsort;
}

Sort repeat_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
{
  Sort bvsort(
      new BVLoggingSort(wrapped_res_sort, op.idx0 * sorts[0]->get_width()));
  return bvsort;
}

Sort int_to_bv_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
{
  Sort bvsort(new BVLoggingSort(wrapped_res_sort, op.idx0));
  return bvsort;
}

Sort apply_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
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

Sort select_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
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

Sort store_sort(Op op, SortVec & sorts, Sort & wrapped_res_sort)
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

}  // namespace smt
