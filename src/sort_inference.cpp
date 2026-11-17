/*!
 * \file sort_inference.cpp
 * \brief Utility functions for checking sortedness and computing the expected
 *        sort when building a term
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * It defines Op::check_sortedness and Op::compute_sort, beside the sort
 * rules of each operator they look up.
 */
#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <iterator>
#include <limits>
#include <memory>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {

namespace {

/** Checks that terms match expected form for quantifiers
 *  To make term traversal easier considering the different
 *  handlings of quantifiers in the API's of underlying
 *  smt-switch requires that quantified terms take the form:
 *  <Forall/Exists> bound_param . body
 *  thus it takes two arguments, the parameter and a formula
 *  containing that parameter
 *  this does not limit expressivity because you can nest them
 *  @param terms the vector of terms
 *  @return true iff the terms match the expected pattern
 *  Note: this is applied directly in check_sortedness because it must
 *  be over terms
 */
bool check_quantifier_terms(const TermVec & terms)
{
  return terms.size() == 2 && terms[0]->is_param()
         && terms[1]->get_sort()->is_boolean();
}

/* helpers for sort checking */

/** Checks that sorts are expected for a quantified term
 *  e.g. that the second argument is of sort Bool
 *  similar to check_quantifier_terms but doesn't check that
 *  first argument is a parameter
 *  @param sorts the vector of sorts
 *  @return true iff the terms match the expected pattern
 *  Note: this is applied directly in compute_sort because it must
 *  be over terms
 */
bool check_quantifier_sorts(const SortVec & sorts)
{
  return sorts.size() == 2 && sorts[1]->is_boolean();
}

/** Checks that the sorts are equivalent
 *  @param sorts a vector of sorts
 *  @return true iff they're all equal, so true for none
 */
bool equal_sorts(const SortVec & sorts)
{
  return (adjacent_find(sorts.begin(), sorts.end(), std::not_equal_to<Sort>())
          == sorts.end());
}

/** Checks that Ite arguments are well-sorted
 *  @param sorts a vector of sorts
 *  @return true iff only the sorts are valid for an ite
 */
bool check_ite_sorts(const SortVec & sorts)
{
  return sorts.size() == 3 && sorts[0]->is_boolean() && sorts[1] == sorts[2];
}

/** Returns true iff all the sorts have SortKind sk
 *  @param sk the expected SortKind
 *  @param sorts the vector of Sorts to check
 *  @return true iff all SortKinds have sort sk
 */
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

/** Returns true iff all the sorts have SortKind in sks
 *  @param sks the set of possible SortKinds
 *  @param sorts the vector of Sorts to check
 *  @return true iff all sorts have SortKind in sks
 */
bool check_one_of_sortkinds(const std::unordered_set<SortKind> & sks,
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

/** Checks if the sorts are well-sorted for an apply operator
 *  @param sorts the vector of sorts
 *  @return true iff the first sort is a function sort
 *         and the rest of the sorts match the domain of the
 *         function
 */
bool check_apply_sorts(const SortVec & sorts)
{
  if (sorts.empty())
  {
    return false;
  }
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

  for (std::size_t i = 0; i < domain_sorts.size(); ++i)
  {
    if (domain_sorts[i] != sorts[i + 1])
    {
      return false;
    }
  }
  return true;
}

/** Checks if the sorts are well-sorted for a select operator
 *  @param sorts the vector of sorts
 *  @param returns true iff the first sort is an array sort
 *         and the second sort is the index sort
 */
bool check_select_sorts(const SortVec & sorts)
{
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

// the selector, then the datatype term it reads
bool check_selector_sorts(const SortVec & sorts)
{
  return sorts.size() == 2 && sorts[0]->get_sort_kind() == SELECTOR
         && sorts[1]->get_sort_kind() == DATATYPE;
}

// the constructor, then its arguments, which only the backend checks
bool check_constructor_sorts(const SortVec & sorts)
{
  return !sorts.empty() && sorts[0]->get_sort_kind() == CONSTRUCTOR;
}

// the tester, then the datatype term it tests
bool check_tester_sorts(const SortVec & sorts)
{
  return sorts.size() == 2 && sorts[0]->get_sort_kind() == TESTER
         && sorts[1]->get_sort_kind() == DATATYPE;
}

/** Checks if the sorts are well-sorted for a store operator
 *  @param sorts the vector of sorts
 *  @param returns true iff the first sort is an array sort
 *         and the next two match the index and element sort
 */
bool check_store_sorts(const SortVec & sorts)
{
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

/** Checks if the sorts are well-sorted for a substring operator
 *  @param sorts the vector of sorts
 *  @param returns true iff the first sort is the string sort
 *         and the next two match the int sort
 */
bool check_substr_sorts(const SortVec & sorts)
{
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

/** Checks if the sorts are well-sorted for a char at operator
 *  @param sorts the vector of sorts
 *  @param returns true iff the first sort is the string sort
 *         and the second is the int sort
 */
bool check_charat_sorts(const SortVec & sorts)
{
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

/** Checks if the sorts are well-sorted for an index of operator
 *  @param sorts the vector of sorts
 *  @param returns true iff the first two sorts are the string sort
 *         and the third is the int sort
 */
bool check_indexof_sorts(const SortVec & sorts)
{
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
  for (const Sort & sort : sorts)
  {
    if (!sort->is_boolean())
    {
      return false;
    }
  }
  return true;
}

bool bv_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(BV, sorts);
}

bool eq_bv_sorts(const SortVec & sorts)
{
  return !sorts.empty() && sorts[0]->get_sort_kind() == BV
         && equal_sorts(sorts);
}

bool real_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(REAL, sorts);
}

bool int_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(INT, sorts);
}

bool string_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(STRING, sorts);
}

bool arithmetic_sorts(const SortVec & sorts)
{
  return check_one_of_sortkinds({ INT, REAL }, sorts);
}

/** Weaker version of equal_sorts
 *  Checks that the sorts are either equivalent
 *  or at least all arithmetic sorts (e.g. real
 *  and integer).
 *  @return true iff they're all arithmetic sorts
 *          or exactly the same sort
 */
bool arith_equal_sorts(const SortVec & sorts)
{
  return equal_sorts(sorts) || arithmetic_sorts(sorts);
}

Sort same_sort(Op, const AbsSmtSolver *, const SortVec & sorts)
{
  return sorts[0];
}

/** @return the Real sort if one of the sorts is the Real sort, and the first
 *  sort otherwise, for an arithmetic operator over Ints and Reals */
Sort arithmetic_sort(Op, const AbsSmtSolver *, const SortVec & sorts)
{
  // over an Int and a Real, every solver of both makes the term a Real
  for (const Sort & sort : sorts)
  {
    if (sort->get_sort_kind() == REAL)
    {
      return sort;
    }
  }
  return sorts[0];
}

Sort bool_sort(Op, const AbsSmtSolver * solver, const SortVec &)
{
  return solver->make_sort(BOOL);
}

Sort single_bit_sort(Op, const AbsSmtSolver * solver, const SortVec &)
{
  return solver->make_sort(BV, 1);
}

Sort real_sort(Op, const AbsSmtSolver * solver, const SortVec &)
{
  return solver->make_sort(REAL);
}

Sort int_sort(Op, const AbsSmtSolver * solver, const SortVec &)
{
  return solver->make_sort(INT);
}

Sort string_sort(Op, const AbsSmtSolver * solver, const SortVec &)
{
  return solver->make_sort(STRING);
}

Sort ite_sort(Op, const AbsSmtSolver *, const SortVec & sorts)
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
  std::uint64_t upper = op.indices[0];
  std::uint64_t lower = op.indices[1];
  std::uint64_t width = sorts[0]->get_width();
  if (lower > upper || upper >= width)
  {
    throw IncorrectUsageException(
        op.to_string() + " needs width > upper >= lower, but its argument has "
        + "width " + std::to_string(width));
  }
  return solver->make_sort(BV, upper - lower + 1);
}

Sort concat_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  constexpr std::uint64_t max = std::numeric_limits<std::uint64_t>::max();
  std::uint64_t width0 = sorts[0]->get_width();
  std::uint64_t width1 = sorts[1]->get_width();
  if (width1 > max - width0)
  {
    throw IncorrectUsageException(op.to_string() + " would be wider than "
                                  + std::to_string(max) + " bits");
  }
  return solver->make_sort(BV, width0 + width1);
}

Sort extend_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  constexpr std::uint64_t max = std::numeric_limits<std::uint64_t>::max();
  std::uint64_t width = sorts[0]->get_width();
  if (op.indices[0] > max - width)
  {
    throw IncorrectUsageException(op.to_string() + " would be wider than "
                                  + std::to_string(max) + " bits");
  }
  return solver->make_sort(BV, op.indices[0] + width);
}

Sort repeat_sort(Op op, const AbsSmtSolver * solver, const SortVec & sorts)
{
  constexpr std::uint64_t max = std::numeric_limits<std::uint64_t>::max();
  std::uint64_t width = sorts[0]->get_width();
  if (width != 0 && op.indices[0] > max / width)
  {
    throw IncorrectUsageException(op.to_string() + " would be wider than "
                                  + std::to_string(max) + " bits");
  }
  return solver->make_sort(BV, op.indices[0] * width);
}

Sort int_to_bv_sort(Op op, const AbsSmtSolver * solver, const SortVec &)
{
  return solver->make_sort(BV, op.indices[0]);
}

Sort apply_sort(Op, const AbsSmtSolver *, const SortVec & sorts)
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

Sort select_sort(Op, const AbsSmtSolver *, const SortVec & sorts)
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

Sort store_sort(Op, const AbsSmtSolver *, const SortVec & sorts)
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

Sort selector_sort(Op, const AbsSmtSolver *, const SortVec & sorts)
{
  return (sorts[0])->get_codomain_sort();
}
Sort constructor_sort(Op, const AbsSmtSolver *, const SortVec & sorts)
{
  return (sorts[0])->get_codomain_sort();
}

/** How check_sortedness checks an operator's argument sorts, by the
 *  function it calls
 */
enum class SortCheck
{
  BOOL,
  ITE,
  ARITH_EQUAL,
  APPLY,
  ARITHMETIC,
  INT,
  REAL,
  BV,
  EQ_BV,
  STRING,
  SUBSTR,
  CHARAT,
  INDEXOF,
  SELECT,
  STORE,
  QUANTIFIER,
  SELECTOR,
  TESTER,
  CONSTRUCTOR,
};

/** How compute_sort computes the sort of an operator's application, by
 *  the function it calls
 */
enum class SortComputation
{
  BOOL,
  ITE,
  APPLY,
  ARITHMETIC,
  SAME,
  REAL,
  INT,
  CONCAT,
  EXTRACT,
  SINGLE_BIT,
  EXTEND,
  REPEAT,
  INT_TO_BV,
  STRING,
  SELECT,
  STORE,
  SELECTOR,
  CONSTRUCTOR,
};

/** The sort rules of an operator */
struct PrimOpSortInfo
{
  PrimOp op;
  SortCheck check;
  SortComputation computation;
};

// one row per PrimOp, in the order of the enum
constexpr PrimOpSortInfo primop_sort_info[] = {
  { And, SortCheck::BOOL, SortComputation::BOOL },
  { Or, SortCheck::BOOL, SortComputation::BOOL },
  { Xor, SortCheck::BOOL, SortComputation::BOOL },
  { Not, SortCheck::BOOL, SortComputation::BOOL },
  { Implies, SortCheck::BOOL, SortComputation::BOOL },
  { Ite, SortCheck::ITE, SortComputation::ITE },
  { Equal, SortCheck::ARITH_EQUAL, SortComputation::BOOL },
  { Distinct, SortCheck::ARITH_EQUAL, SortComputation::BOOL },
  { Apply, SortCheck::APPLY, SortComputation::APPLY },
  { Plus, SortCheck::ARITHMETIC, SortComputation::ARITHMETIC },
  { Minus, SortCheck::ARITHMETIC, SortComputation::ARITHMETIC },
  { Negate, SortCheck::ARITHMETIC, SortComputation::SAME },
  { Mult, SortCheck::ARITHMETIC, SortComputation::ARITHMETIC },
  { Div, SortCheck::ARITHMETIC, SortComputation::REAL },
  { Lt, SortCheck::ARITHMETIC, SortComputation::BOOL },
  { Le, SortCheck::ARITHMETIC, SortComputation::BOOL },
  { Gt, SortCheck::ARITHMETIC, SortComputation::BOOL },
  { Ge, SortCheck::ARITHMETIC, SortComputation::BOOL },
  { Mod, SortCheck::INT, SortComputation::INT },
  // technically Abs/Pow only defined for integers in
  // SMT-LIB but not sure if that's true for all solvers
  // might also be good to be forward looking
  { Abs, SortCheck::INT, SortComputation::SAME },
  { Pow, SortCheck::INT, SortComputation::SAME },
  { IntDiv, SortCheck::INT, SortComputation::INT },
  { Divisible, SortCheck::INT, SortComputation::BOOL },
  { To_Real, SortCheck::INT, SortComputation::REAL },
  { To_Int, SortCheck::REAL, SortComputation::INT },
  { Is_Int, SortCheck::REAL, SortComputation::BOOL },
  { Concat, SortCheck::BV, SortComputation::CONCAT },
  { Extract, SortCheck::BV, SortComputation::EXTRACT },
  { BVNot, SortCheck::BV, SortComputation::SAME },
  { BVNeg, SortCheck::BV, SortComputation::SAME },
  { BVAnd, SortCheck::EQ_BV, SortComputation::SAME },
  { BVOr, SortCheck::EQ_BV, SortComputation::SAME },
  { BVXor, SortCheck::EQ_BV, SortComputation::SAME },
  { BVNand, SortCheck::EQ_BV, SortComputation::SAME },
  { BVNor, SortCheck::EQ_BV, SortComputation::SAME },
  { BVXnor, SortCheck::EQ_BV, SortComputation::SAME },
  { BVAdd, SortCheck::EQ_BV, SortComputation::SAME },
  { BVSub, SortCheck::EQ_BV, SortComputation::SAME },
  { BVMul, SortCheck::EQ_BV, SortComputation::SAME },
  { BVUdiv, SortCheck::EQ_BV, SortComputation::SAME },
  { BVSdiv, SortCheck::EQ_BV, SortComputation::SAME },
  { BVUrem, SortCheck::EQ_BV, SortComputation::SAME },
  { BVSrem, SortCheck::EQ_BV, SortComputation::SAME },
  { BVSmod, SortCheck::EQ_BV, SortComputation::SAME },
  { BVShl, SortCheck::EQ_BV, SortComputation::SAME },
  { BVAshr, SortCheck::EQ_BV, SortComputation::SAME },
  { BVLshr, SortCheck::EQ_BV, SortComputation::SAME },
  { BVComp, SortCheck::EQ_BV, SortComputation::SINGLE_BIT },
  { BVUlt, SortCheck::EQ_BV, SortComputation::BOOL },
  { BVUle, SortCheck::EQ_BV, SortComputation::BOOL },
  { BVUgt, SortCheck::EQ_BV, SortComputation::BOOL },
  { BVUge, SortCheck::EQ_BV, SortComputation::BOOL },
  { BVSlt, SortCheck::EQ_BV, SortComputation::BOOL },
  { BVSle, SortCheck::EQ_BV, SortComputation::BOOL },
  { BVSgt, SortCheck::EQ_BV, SortComputation::BOOL },
  { BVSge, SortCheck::EQ_BV, SortComputation::BOOL },
  { Zero_Extend, SortCheck::BV, SortComputation::EXTEND },
  { Sign_Extend, SortCheck::BV, SortComputation::EXTEND },
  { Repeat, SortCheck::BV, SortComputation::REPEAT },
  { Rotate_Left, SortCheck::BV, SortComputation::SAME },
  { Rotate_Right, SortCheck::BV, SortComputation::SAME },
  { BV_To_Nat, SortCheck::BV, SortComputation::INT },
  { UBV_To_Int, SortCheck::BV, SortComputation::INT },
  { SBV_To_Int, SortCheck::BV, SortComputation::INT },
  { Int_To_BV, SortCheck::INT, SortComputation::INT_TO_BV },
  { StrLt, SortCheck::STRING, SortComputation::BOOL },
  { StrLeq, SortCheck::STRING, SortComputation::BOOL },
  { StrLen, SortCheck::STRING, SortComputation::INT },
  { StrConcat, SortCheck::STRING, SortComputation::STRING },
  { StrSubstr, SortCheck::SUBSTR, SortComputation::STRING },
  { StrAt, SortCheck::CHARAT, SortComputation::STRING },
  { StrContains, SortCheck::STRING, SortComputation::BOOL },
  { StrIndexof, SortCheck::INDEXOF, SortComputation::INT },
  { StrReplace, SortCheck::STRING, SortComputation::STRING },
  { StrReplaceAll, SortCheck::STRING, SortComputation::STRING },
  { StrPrefixof, SortCheck::STRING, SortComputation::BOOL },
  { StrSuffixof, SortCheck::STRING, SortComputation::BOOL },
  { StrIsDigit, SortCheck::STRING, SortComputation::BOOL },
  { Select, SortCheck::SELECT, SortComputation::SELECT },
  { Store, SortCheck::STORE, SortComputation::STORE },
  { Forall, SortCheck::QUANTIFIER, SortComputation::BOOL },
  { Exists, SortCheck::QUANTIFIER, SortComputation::BOOL },
  { Apply_Selector, SortCheck::SELECTOR, SortComputation::SELECTOR },
  { Apply_Tester, SortCheck::TESTER, SortComputation::BOOL },
  { Apply_Constructor, SortCheck::CONSTRUCTOR, SortComputation::CONSTRUCTOR },
};

static_assert(std::size(primop_sort_info) == NUM_OPS_AND_NULL,
              "primop_sort_info needs one row per PrimOp");

constexpr bool rows_follow_enum()
{
  for (std::size_t i = 0; i < std::size(primop_sort_info); ++i)
  {
    if (primop_sort_info[i].op != static_cast<PrimOp>(i))
    {
      return false;
    }
  }
  return true;
}
static_assert(
    rows_follow_enum(),
    "primop_sort_info's rows must be in the order of the PrimOp enum");

/** The sort rules of po
 *  @param caller the public function asking, for the message
 *  @throws IncorrectUsageException for NUM_OPS_AND_NULL or an out-of-range
 *          value
 */
const PrimOpSortInfo & sort_info(PrimOp po, const char * caller)
{
  auto i = static_cast<std::size_t>(po);
  if (i >= std::size(primop_sort_info))
  {
    throw IncorrectUsageException(std::string(caller)
                                  + " got a PrimOp that is not an operator: "
                                  + std::to_string(static_cast<int>(po)));
  }
  return primop_sort_info[i];
}

bool check_sorts(SortCheck check, const SortVec & sorts)
{
  switch (check)
  {
    case SortCheck::BOOL: return bool_sorts(sorts);
    case SortCheck::ITE: return check_ite_sorts(sorts);
    case SortCheck::ARITH_EQUAL: return arith_equal_sorts(sorts);
    case SortCheck::APPLY: return check_apply_sorts(sorts);
    case SortCheck::ARITHMETIC: return arithmetic_sorts(sorts);
    case SortCheck::INT: return int_sorts(sorts);
    case SortCheck::REAL: return real_sorts(sorts);
    case SortCheck::BV: return bv_sorts(sorts);
    case SortCheck::EQ_BV: return eq_bv_sorts(sorts);
    case SortCheck::STRING: return string_sorts(sorts);
    case SortCheck::SUBSTR: return check_substr_sorts(sorts);
    case SortCheck::CHARAT: return check_charat_sorts(sorts);
    case SortCheck::INDEXOF: return check_indexof_sorts(sorts);
    case SortCheck::SELECT: return check_select_sorts(sorts);
    case SortCheck::STORE: return check_store_sorts(sorts);
    case SortCheck::QUANTIFIER: return check_quantifier_sorts(sorts);
    case SortCheck::SELECTOR: return check_selector_sorts(sorts);
    case SortCheck::TESTER: return check_tester_sorts(sorts);
    case SortCheck::CONSTRUCTOR: return check_constructor_sorts(sorts);
  }
  throw InternalException("check_sortedness got an out-of-range SortCheck");
}

Sort compute(SortComputation computation,
             Op op,
             const AbsSmtSolver * solver,
             const SortVec & sorts)
{
  switch (computation)
  {
    case SortComputation::BOOL: return bool_sort(op, solver, sorts);
    case SortComputation::ITE: return ite_sort(op, solver, sorts);
    case SortComputation::APPLY: return apply_sort(op, solver, sorts);
    case SortComputation::ARITHMETIC: return arithmetic_sort(op, solver, sorts);
    case SortComputation::SAME: return same_sort(op, solver, sorts);
    case SortComputation::REAL: return real_sort(op, solver, sorts);
    case SortComputation::INT: return int_sort(op, solver, sorts);
    case SortComputation::CONCAT: return concat_sort(op, solver, sorts);
    case SortComputation::EXTRACT: return extract_sort(op, solver, sorts);
    case SortComputation::SINGLE_BIT: return single_bit_sort(op, solver, sorts);
    case SortComputation::EXTEND: return extend_sort(op, solver, sorts);
    case SortComputation::REPEAT: return repeat_sort(op, solver, sorts);
    case SortComputation::INT_TO_BV: return int_to_bv_sort(op, solver, sorts);
    case SortComputation::STRING: return string_sort(op, solver, sorts);
    case SortComputation::SELECT: return select_sort(op, solver, sorts);
    case SortComputation::STORE: return store_sort(op, solver, sorts);
    case SortComputation::SELECTOR: return selector_sort(op, solver, sorts);
    case SortComputation::CONSTRUCTOR:
      return constructor_sort(op, solver, sorts);
  }
  throw InternalException("compute_sort got an out-of-range SortComputation");
}

}  // namespace

bool Op::check_sortedness(const TermVec & terms) const
{
  PrimOp po = prim_op;
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
  return check_sortedness(sorts);
}

bool Op::check_sortedness(const SortVec & sorts) const
{
  auto min_max_arity = get_arity(prim_op);
  std::size_t num_args = sorts.size();
  if (num_args < min_max_arity.first || num_args > min_max_arity.second)
  {
    // wrong number of arguments
    return false;
  }

  return check_sorts(sort_info(prim_op, "check_sortedness").check, sorts);
}

Sort Op::compute_sort(const AbsSmtSolver * solver, const TermVec & terms) const
{
  SortVec sorts;
  for (auto t : terms)
  {
    sorts.push_back(t->get_sort());
  }
  return compute_sort(solver, sorts);
}

Sort Op::compute_sort(const AbsSmtSolver * solver, const SortVec & sorts) const
{
  // Only too few arguments are refused, since a backend may take more than
  // SMT-LIB defines, such as a quantifier binding several params.
  std::size_t min_arity = get_arity(prim_op).first;
  if (sorts.size() < min_arity)
  {
    throw IncorrectUsageException(
        to_string() + " takes at least " + std::to_string(min_arity)
        + " arguments, but got " + std::to_string(sorts.size()));
  }
  return compute(
      sort_info(prim_op, "compute_sort").computation, *this, solver, sorts);
}

Sort Op::compute_sort(const SmtSolver & solver, const TermVec & terms) const
{
  return compute_sort(solver.get(), terms);
}

Sort Op::compute_sort(const SmtSolver & solver, const SortVec & sorts) const
{
  return compute_sort(solver.get(), sorts);
}

}  // namespace smt
