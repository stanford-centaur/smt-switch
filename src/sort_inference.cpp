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

// The solver a rule makes the computed sort with
using SolverPtr = std::shared_ptr<const AbsSmtSolver>;

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
    if (sk != sort->get_kind())
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
    if (sks.find(sort->get_kind()) == sks.end())
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
  if (funsort->get_kind() != SortKind::FUNCTION)
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
  if (arrsort->get_kind() != SortKind::ARRAY)
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
  return sorts.size() == 2 && sorts[0]->get_kind() == SortKind::SELECTOR
         && sorts[1]->get_kind() == SortKind::DATATYPE;
}

// the constructor, then its arguments, which only the backend checks
bool check_constructor_sorts(const SortVec & sorts)
{
  return !sorts.empty() && sorts[0]->get_kind() == SortKind::CONSTRUCTOR;
}

// the tester, then the datatype term it tests
bool check_tester_sorts(const SortVec & sorts)
{
  return sorts.size() == 2 && sorts[0]->get_kind() == SortKind::TESTER
         && sorts[1]->get_kind() == SortKind::DATATYPE;
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
  if (arrsort->get_kind() != SortKind::ARRAY)
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
  if (strsort->get_kind() != SortKind::STRING)
  {
    return false;
  }

  if (sorts[1]->get_kind() != SortKind::INT)
  {
    return false;
  }
  else if (sorts[2]->get_kind() != SortKind::INT)
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
  if (strsort->get_kind() != SortKind::STRING)
  {
    return false;
  }

  if (sorts[1]->get_kind() != SortKind::INT)
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
  if (strsort->get_kind() != SortKind::STRING)
  {
    return false;
  }

  if (sorts[1]->get_kind() != SortKind::STRING)
  {
    return false;
  }
  else if (sorts[2]->get_kind() != SortKind::INT)
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
  return check_sortkind_matches(SortKind::BV, sorts);
}

bool eq_bv_sorts(const SortVec & sorts)
{
  return !sorts.empty() && sorts[0]->get_kind() == SortKind::BV
         && equal_sorts(sorts);
}

bool real_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(SortKind::REAL, sorts);
}

bool int_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(SortKind::INT, sorts);
}

bool string_sorts(const SortVec & sorts)
{
  return check_sortkind_matches(SortKind::STRING, sorts);
}

bool arithmetic_sorts(const SortVec & sorts)
{
  return check_one_of_sortkinds({ SortKind::INT, SortKind::REAL }, sorts);
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

Sort same_sort(Op, const SolverPtr &, const SortVec & sorts)
{
  return sorts[0];
}

/** @return the Real sort if one of the sorts is the Real sort, and the first
 *  sort otherwise, for an arithmetic operator over Ints and Reals */
Sort arithmetic_sort(Op, const SolverPtr &, const SortVec & sorts)
{
  // over an Int and a Real, every solver of both makes the term a Real
  for (const Sort & sort : sorts)
  {
    if (sort->get_kind() == SortKind::REAL)
    {
      return sort;
    }
  }
  return sorts[0];
}

Sort bool_sort(Op, const SolverPtr & solver, const SortVec &)
{
  return solver->make_sort(SortKind::BOOL);
}

Sort single_bit_sort(Op, const SolverPtr & solver, const SortVec &)
{
  return solver->make_sort(SortKind::BV, 1);
}

Sort real_sort(Op, const SolverPtr & solver, const SortVec &)
{
  return solver->make_sort(SortKind::REAL);
}

Sort int_sort(Op, const SolverPtr & solver, const SortVec &)
{
  return solver->make_sort(SortKind::INT);
}

Sort string_sort(Op, const SolverPtr & solver, const SortVec &)
{
  return solver->make_sort(SortKind::STRING);
}

Sort ite_sort(Op, const SolverPtr &, const SortVec & sorts)
{
  if (sorts[1] != sorts[2])
  {
    throw IncorrectUsageException("Ite element sorts don't match: "
                                  + sorts[1]->to_string() + ", "
                                  + sorts[2]->to_string());
  }
  return sorts[1];
}

Sort extract_sort(Op op, const SolverPtr & solver, const SortVec & sorts)
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
  return solver->make_sort(SortKind::BV, upper - lower + 1);
}

Sort concat_sort(Op op, const SolverPtr & solver, const SortVec & sorts)
{
  constexpr std::uint64_t max = std::numeric_limits<std::uint64_t>::max();
  std::uint64_t width0 = sorts[0]->get_width();
  std::uint64_t width1 = sorts[1]->get_width();
  if (width1 > max - width0)
  {
    throw IncorrectUsageException(op.to_string() + " would be wider than "
                                  + std::to_string(max) + " bits");
  }
  return solver->make_sort(SortKind::BV, width0 + width1);
}

Sort extend_sort(Op op, const SolverPtr & solver, const SortVec & sorts)
{
  constexpr std::uint64_t max = std::numeric_limits<std::uint64_t>::max();
  std::uint64_t width = sorts[0]->get_width();
  if (op.indices[0] > max - width)
  {
    throw IncorrectUsageException(op.to_string() + " would be wider than "
                                  + std::to_string(max) + " bits");
  }
  return solver->make_sort(SortKind::BV, op.indices[0] + width);
}

Sort repeat_sort(Op op, const SolverPtr & solver, const SortVec & sorts)
{
  constexpr std::uint64_t max = std::numeric_limits<std::uint64_t>::max();
  std::uint64_t width = sorts[0]->get_width();
  if (width != 0 && op.indices[0] > max / width)
  {
    throw IncorrectUsageException(op.to_string() + " would be wider than "
                                  + std::to_string(max) + " bits");
  }
  return solver->make_sort(SortKind::BV, op.indices[0] * width);
}

Sort int_to_bv_sort(Op op, const SolverPtr & solver, const SortVec &)
{
  return solver->make_sort(SortKind::BV, op.indices[0]);
}

Sort apply_sort(Op, const SolverPtr &, const SortVec & sorts)
{
  Sort funsort = sorts[0];
  if (funsort->get_kind() != SortKind::FUNCTION)
  {
    throw IncorrectUsageException(
        "Expecting first argument to Apply to be a function but got "
        + funsort->to_string());
  }
  return funsort->get_codomain_sort();
}

Sort select_sort(Op, const SolverPtr &, const SortVec & sorts)
{
  Sort arraysort = sorts[0];
  if (arraysort->get_kind() != SortKind::ARRAY)
  {
    throw IncorrectUsageException(
        "Expecting first argument of Select to be an array but got: "
        + arraysort->to_string());
  }
  return arraysort->get_elemsort();
}

Sort store_sort(Op, const SolverPtr &, const SortVec & sorts)
{
  Sort arraysort = sorts[0];
  if (arraysort->get_kind() != SortKind::ARRAY)
  {
    throw IncorrectUsageException(
        "Expecting first argument of Store to be an array but got: "
        + arraysort->to_string());
  }
  return arraysort;
}

Sort selector_sort(Op, const SolverPtr &, const SortVec & sorts)
{
  return (sorts[0])->get_codomain_sort();
}
Sort constructor_sort(Op, const SolverPtr &, const SortVec & sorts)
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
struct KindSortInfo
{
  Op::Kind kind;
  SortCheck check;
  SortComputation computation;
};

// one row per kind but Op::NONE, in the order of the enum
constexpr KindSortInfo kind_sort_info[] = {
  { Op::And, SortCheck::BOOL, SortComputation::BOOL },
  { Op::Or, SortCheck::BOOL, SortComputation::BOOL },
  { Op::Xor, SortCheck::BOOL, SortComputation::BOOL },
  { Op::Not, SortCheck::BOOL, SortComputation::BOOL },
  { Op::Implies, SortCheck::BOOL, SortComputation::BOOL },
  { Op::Ite, SortCheck::ITE, SortComputation::ITE },
  { Op::Equal, SortCheck::ARITH_EQUAL, SortComputation::BOOL },
  { Op::Distinct, SortCheck::ARITH_EQUAL, SortComputation::BOOL },
  { Op::Apply, SortCheck::APPLY, SortComputation::APPLY },
  { Op::Plus, SortCheck::ARITHMETIC, SortComputation::ARITHMETIC },
  { Op::Minus, SortCheck::ARITHMETIC, SortComputation::ARITHMETIC },
  { Op::Negate, SortCheck::ARITHMETIC, SortComputation::SAME },
  { Op::Mult, SortCheck::ARITHMETIC, SortComputation::ARITHMETIC },
  { Op::Div, SortCheck::ARITHMETIC, SortComputation::REAL },
  { Op::Lt, SortCheck::ARITHMETIC, SortComputation::BOOL },
  { Op::Le, SortCheck::ARITHMETIC, SortComputation::BOOL },
  { Op::Gt, SortCheck::ARITHMETIC, SortComputation::BOOL },
  { Op::Ge, SortCheck::ARITHMETIC, SortComputation::BOOL },
  { Op::Mod, SortCheck::INT, SortComputation::INT },
  // technically Abs/Pow only defined for integers in
  // SMT-LIB but not sure if that's true for all solvers
  // might also be good to be forward looking
  { Op::Abs, SortCheck::INT, SortComputation::SAME },
  { Op::Pow, SortCheck::INT, SortComputation::SAME },
  { Op::IntDiv, SortCheck::INT, SortComputation::INT },
  { Op::Divisible, SortCheck::INT, SortComputation::BOOL },
  { Op::To_Real, SortCheck::INT, SortComputation::REAL },
  { Op::To_Int, SortCheck::REAL, SortComputation::INT },
  { Op::Is_Int, SortCheck::REAL, SortComputation::BOOL },
  { Op::Concat, SortCheck::BV, SortComputation::CONCAT },
  { Op::Extract, SortCheck::BV, SortComputation::EXTRACT },
  { Op::BVNot, SortCheck::BV, SortComputation::SAME },
  { Op::BVNeg, SortCheck::BV, SortComputation::SAME },
  { Op::BVAnd, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVOr, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVXor, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVNand, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVNor, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVXnor, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVAdd, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVSub, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVMul, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVUdiv, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVSdiv, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVUrem, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVSrem, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVSmod, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVShl, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVAshr, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVLshr, SortCheck::EQ_BV, SortComputation::SAME },
  { Op::BVComp, SortCheck::EQ_BV, SortComputation::SINGLE_BIT },
  { Op::BVUlt, SortCheck::EQ_BV, SortComputation::BOOL },
  { Op::BVUle, SortCheck::EQ_BV, SortComputation::BOOL },
  { Op::BVUgt, SortCheck::EQ_BV, SortComputation::BOOL },
  { Op::BVUge, SortCheck::EQ_BV, SortComputation::BOOL },
  { Op::BVSlt, SortCheck::EQ_BV, SortComputation::BOOL },
  { Op::BVSle, SortCheck::EQ_BV, SortComputation::BOOL },
  { Op::BVSgt, SortCheck::EQ_BV, SortComputation::BOOL },
  { Op::BVSge, SortCheck::EQ_BV, SortComputation::BOOL },
  { Op::Zero_Extend, SortCheck::BV, SortComputation::EXTEND },
  { Op::Sign_Extend, SortCheck::BV, SortComputation::EXTEND },
  { Op::Repeat, SortCheck::BV, SortComputation::REPEAT },
  { Op::Rotate_Left, SortCheck::BV, SortComputation::SAME },
  { Op::Rotate_Right, SortCheck::BV, SortComputation::SAME },
  { Op::UBV_To_Int, SortCheck::BV, SortComputation::INT },
  { Op::SBV_To_Int, SortCheck::BV, SortComputation::INT },
  { Op::Int_To_BV, SortCheck::INT, SortComputation::INT_TO_BV },
  { Op::StrLt, SortCheck::STRING, SortComputation::BOOL },
  { Op::StrLeq, SortCheck::STRING, SortComputation::BOOL },
  { Op::StrLen, SortCheck::STRING, SortComputation::INT },
  { Op::StrConcat, SortCheck::STRING, SortComputation::STRING },
  { Op::StrSubstr, SortCheck::SUBSTR, SortComputation::STRING },
  { Op::StrAt, SortCheck::CHARAT, SortComputation::STRING },
  { Op::StrContains, SortCheck::STRING, SortComputation::BOOL },
  { Op::StrIndexof, SortCheck::INDEXOF, SortComputation::INT },
  { Op::StrReplace, SortCheck::STRING, SortComputation::STRING },
  { Op::StrReplaceAll, SortCheck::STRING, SortComputation::STRING },
  { Op::StrPrefixof, SortCheck::STRING, SortComputation::BOOL },
  { Op::StrSuffixof, SortCheck::STRING, SortComputation::BOOL },
  { Op::StrIsDigit, SortCheck::STRING, SortComputation::BOOL },
  { Op::Select, SortCheck::SELECT, SortComputation::SELECT },
  { Op::Store, SortCheck::STORE, SortComputation::STORE },
  { Op::Forall, SortCheck::QUANTIFIER, SortComputation::BOOL },
  { Op::Exists, SortCheck::QUANTIFIER, SortComputation::BOOL },
  { Op::Apply_Selector, SortCheck::SELECTOR, SortComputation::SELECTOR },
  { Op::Apply_Tester, SortCheck::TESTER, SortComputation::BOOL },
  { Op::Apply_Constructor,
    SortCheck::CONSTRUCTOR,
    SortComputation::CONSTRUCTOR },
};

static_assert(std::size(kind_sort_info) == Op::num_kinds - 1,
              "kind_sort_info needs one row per kind but Op::NONE");

constexpr bool rows_follow_enum()
{
  for (std::size_t i = 0; i < std::size(kind_sort_info); ++i)
  {
    if (kind_sort_info[i].kind != static_cast<Op::Kind>(i + 1))
    {
      return false;
    }
  }
  return true;
}
static_assert(rows_follow_enum(),
              "kind_sort_info's rows must be in the order of Op::Kind");

/** The sort rules of kind
 *  @param caller the public function asking, for the message
 *  @throws IncorrectUsageException for Op::NONE or an out-of-range value
 */
const KindSortInfo & sort_info(Op::Kind kind, const char * caller)
{
  auto i = static_cast<std::size_t>(kind);
  if (kind == Op::NONE || i >= Op::num_kinds)
  {
    throw IncorrectUsageException(std::string(caller)
                                  + " got a kind that is not an operator: "
                                  + std::to_string(static_cast<int>(kind)));
  }
  return kind_sort_info[i - 1];
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
             const SolverPtr & solver,
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
  if (kind_ == Op::Forall || kind_ == Op::Exists)
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
  auto min_max_arity = get_arity(kind_);
  std::size_t num_args = sorts.size();
  if (num_args < min_max_arity.first || num_args > min_max_arity.second)
  {
    // wrong number of arguments
    return false;
  }

  return check_sorts(sort_info(kind_, "check_sortedness").check, sorts);
}

Sort Op::compute_sort(const std::shared_ptr<const AbsSmtSolver> & solver,
                      const TermVec & terms) const
{
  SortVec sorts;
  for (auto t : terms)
  {
    sorts.push_back(t->get_sort());
  }
  return compute_sort(solver, sorts);
}

Sort Op::compute_sort(const std::shared_ptr<const AbsSmtSolver> & solver,
                      const SortVec & sorts) const
{
  // Only too few arguments are refused, since a backend may take more than
  // SMT-LIB defines, such as a quantifier binding several params.
  std::size_t min_arity = get_arity(kind_).first;
  if (sorts.size() < min_arity)
  {
    throw IncorrectUsageException(
        to_string() + " takes at least " + std::to_string(min_arity)
        + " arguments, but got " + std::to_string(sorts.size()));
  }
  return compute(
      sort_info(kind_, "compute_sort").computation, *this, solver, sorts);
}

}  // namespace smt
