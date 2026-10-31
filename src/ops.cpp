/*********************                                                        */
/*! \file ops.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief All the builtin operators.
**
**
**/

#include "ops.h"

#include <climits>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <string>
#include <utility>

#include "exceptions.h"

namespace smt {

namespace {

/** The SMT-LIB attribute that defines an operator's application to more
 *  than two arguments
 */
enum class Assoc
{
  NONE,
  LEFT,
  RIGHT,
  CHAINABLE,
  PAIRWISE,
};

/** What SMT-LIB defines for an operator */
struct PrimOpInfo
{
  PrimOp op;
  const char * name;
  Theory theory;
  std::uint64_t num_indices;
  std::size_t min_arity;
  std::size_t max_arity;
  Assoc assoc;
};

// one row per PrimOp, in the order of the enum
constexpr PrimOpInfo primop_info[] = {
  { And, "and", Theory::CORE, 0, 2, INT_MAX, Assoc::LEFT },
  { Or, "or", Theory::CORE, 0, 2, INT_MAX, Assoc::LEFT },
  { Xor, "xor", Theory::CORE, 0, 2, INT_MAX, Assoc::LEFT },
  { Not, "not", Theory::CORE, 0, 1, 1, Assoc::NONE },
  { Implies, "=>", Theory::CORE, 0, 2, INT_MAX, Assoc::RIGHT },
  { Ite, "ite", Theory::CORE, 0, 3, 3, Assoc::NONE },
  { Equal, "=", Theory::CORE, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { Distinct, "distinct", Theory::CORE, 0, 2, INT_MAX, Assoc::PAIRWISE },
  // at least the function and one argument
  // of course, to be well-sorted the number of arguments must
  // match the function domain
  { Apply, "apply", Theory::UF, 0, 2, INT_MAX, Assoc::NONE },
  { Plus, "+", Theory::ARITH, 0, 2, INT_MAX, Assoc::LEFT },
  { Minus, "-", Theory::ARITH, 0, 2, INT_MAX, Assoc::LEFT },
  { Negate, "-", Theory::ARITH, 0, 1, 1, Assoc::NONE },
  { Mult, "*", Theory::ARITH, 0, 2, INT_MAX, Assoc::LEFT },
  { Div, "/", Theory::REALS, 0, 2, INT_MAX, Assoc::LEFT },
  { Lt, "<", Theory::ARITH, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { Le, "<=", Theory::ARITH, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { Gt, ">", Theory::ARITH, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { Ge, ">=", Theory::ARITH, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { Mod, "mod", Theory::INTS, 0, 2, 2, Assoc::NONE },
  { Abs, "abs", Theory::INTS, 0, 1, 1, Assoc::NONE },
  { Pow, "pow", Theory::INTS, 0, 2, 2, Assoc::NONE },
  { IntDiv, "div", Theory::INTS, 0, 2, INT_MAX, Assoc::LEFT },
  { To_Real, "to_real", Theory::REALS_INTS, 0, 1, 1, Assoc::NONE },
  { To_Int, "to_int", Theory::REALS_INTS, 0, 1, 1, Assoc::NONE },
  { Is_Int, "is_int", Theory::REALS_INTS, 0, 1, 1, Assoc::NONE },
  { Concat, "concat", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Extract, "extract", Theory::BITVECTORS, 2, 1, 1, Assoc::NONE },
  { BVNot, "bvnot", Theory::BITVECTORS, 0, 1, 1, Assoc::NONE },
  { BVNeg, "bvneg", Theory::BITVECTORS, 0, 1, 1, Assoc::NONE },
  { BVAnd, "bvand", Theory::BITVECTORS, 0, 2, INT_MAX, Assoc::LEFT },
  { BVOr, "bvor", Theory::BITVECTORS, 0, 2, INT_MAX, Assoc::LEFT },
  { BVXor, "bvxor", Theory::BITVECTORS, 0, 2, INT_MAX, Assoc::LEFT },
  { BVNand, "bvnand", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVNor, "bvnor", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVXnor, "bvxnor", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVAdd, "bvadd", Theory::BITVECTORS, 0, 2, INT_MAX, Assoc::LEFT },
  { BVSub, "bvsub", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVMul, "bvmul", Theory::BITVECTORS, 0, 2, INT_MAX, Assoc::LEFT },
  { BVUdiv, "bvudiv", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVSdiv, "bvsdiv", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVUrem, "bvurem", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVSrem, "bvsrem", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVSmod, "bvsmod", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVShl, "bvshl", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVAshr, "bvashr", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVLshr, "bvlshr", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVComp, "bvcomp", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVUlt, "bvult", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVUle, "bvule", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVUgt, "bvugt", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVUge, "bvuge", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVSlt, "bvslt", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVSle, "bvsle", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVSgt, "bvsgt", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { BVSge, "bvsge", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Zero_Extend, "zero_extend", Theory::BITVECTORS, 1, 1, 1, Assoc::NONE },
  { Sign_Extend, "sign_extend", Theory::BITVECTORS, 1, 1, 1, Assoc::NONE },
  { Repeat, "repeat", Theory::BITVECTORS, 1, 1, 1, Assoc::NONE },
  { Rotate_Left, "rotate_left", Theory::BITVECTORS, 1, 1, 1, Assoc::NONE },
  { Rotate_Right, "rotate_right", Theory::BITVECTORS, 1, 1, 1, Assoc::NONE },
  { BV_To_Nat, "ubv_to_int", Theory::BITVECTORS, 0, 1, 1, Assoc::NONE },
  { UBV_To_Int, "ubv_to_int", Theory::BITVECTORS, 0, 1, 1, Assoc::NONE },
  { SBV_To_Int, "sbv_to_int", Theory::BITVECTORS, 0, 1, 1, Assoc::NONE },
  { Int_To_BV, "int_to_bv", Theory::BITVECTORS, 1, 1, 1, Assoc::NONE },
  { StrLt, "str.<", Theory::STRINGS, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { StrLeq, "str.<=", Theory::STRINGS, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { StrLen, "str.len", Theory::STRINGS, 0, 1, 1, Assoc::NONE },
  { StrConcat, "str.++", Theory::STRINGS, 0, 2, INT_MAX, Assoc::LEFT },
  { StrSubstr, "str.substr", Theory::STRINGS, 0, 3, 3, Assoc::NONE },
  { StrAt, "str.at", Theory::STRINGS, 0, 2, 2, Assoc::NONE },
  { StrContains, "str.contains", Theory::STRINGS, 0, 2, 2, Assoc::NONE },
  { StrIndexof, "str.indexof", Theory::STRINGS, 0, 3, 3, Assoc::NONE },
  { StrReplace, "str.replace", Theory::STRINGS, 0, 3, 3, Assoc::NONE },
  { StrReplaceAll, "str.replace_all", Theory::STRINGS, 0, 3, 3, Assoc::NONE },
  { StrPrefixof, "str.prefixof", Theory::STRINGS, 0, 2, 2, Assoc::NONE },
  { StrSuffixof, "str.suffixof", Theory::STRINGS, 0, 2, 2, Assoc::NONE },
  { StrIsDigit, "str.is_digit", Theory::STRINGS, 0, 1, 1, Assoc::NONE },
  { Select, "select", Theory::ARRAYS, 0, 2, 2, Assoc::NONE },
  { Store, "store", Theory::ARRAYS, 0, 3, 3, Assoc::NONE },
  // to make term traversal easier considering the differences
  // in the underlying solver's handling of quantifiers, smt-switch
  // always uses the form <Forall/Exists> bound_param . body
  // i.e. it takes two arguments, the parameter to bind and the body
  { Forall, "forall", Theory::QUANTIFIERS, 0, 2, 2, Assoc::NONE },
  { Exists, "exists", Theory::QUANTIFIERS, 0, 2, 2, Assoc::NONE },
  { Apply_Selector, "apply_selector", Theory::DATATYPES, 0, 2, 2, Assoc::NONE },
  { Apply_Tester, "apply_tester", Theory::DATATYPES, 0, 2, 2, Assoc::NONE },
  // a nullary constructor is applied to nothing but itself
  { Apply_Constructor,
    "apply_constructor",
    Theory::DATATYPES,
    0,
    1,
    INT_MAX,
    Assoc::NONE },
};

static_assert(std::size(primop_info) == NUM_OPS_AND_NULL,
              "primop_info needs one row per PrimOp");

constexpr bool rows_follow_enum()
{
  for (std::size_t i = 0; i < std::size(primop_info); ++i)
  {
    if (primop_info[i].op != static_cast<PrimOp>(i))
    {
      return false;
    }
  }
  return true;
}
static_assert(rows_follow_enum(),
              "primop_info's rows must be in the order of the PrimOp enum");

/** The row of po, or null for NUM_OPS_AND_NULL or an out-of-range value */
const PrimOpInfo * find_info(PrimOp po)
{
  auto i = static_cast<std::size_t>(po);
  return i < std::size(primop_info) ? &primop_info[i] : nullptr;
}

/** The row of po
 *  @param caller the public function asking, for the message
 *  @throws IncorrectUsageException for NUM_OPS_AND_NULL or an out-of-range
 *          value
 */
const PrimOpInfo & info(PrimOp po, const char * caller)
{
  const PrimOpInfo * row = find_info(po);
  if (!row)
  {
    throw IncorrectUsageException(std::string(caller)
                                  + " got a PrimOp that is no operator: "
                                  + std::to_string(static_cast<int>(po)));
  }
  return *row;
}

/** The attribute of po, NONE if it has no row */
Assoc assoc_of(PrimOp po)
{
  const PrimOpInfo * row = find_info(po);
  return row ? row->assoc : Assoc::NONE;
}

}  // namespace

std::string to_string(PrimOp op)
{
  if (op == NUM_OPS_AND_NULL)
  {
    return "null";
  }
  return info(op, "to_string").name;
}

Op::Op(PrimOp o) : prim_op(o) {}
Op::Op(PrimOp o, std::uint64_t index0) : prim_op(o), num_idx(1), idx0(index0) {}
Op::Op(PrimOp o, std::uint64_t index0, std::uint64_t index1)
    : prim_op(o), num_idx(2), idx0(index0), idx1(index1)
{
}

std::string Op::to_string() const
{
  std::string res;
  if (num_idx)
  {
    res += "(_ ";
  }

  res += smt::to_string(prim_op);

  if (num_idx >= 1)
  {
    res += " " + std::to_string(idx0);
  }
  if (num_idx >= 2)
  {
    res += " " + std::to_string(idx1);
  }
  if (num_idx)
  {
    res += ")";
  }
  return res;
}

bool Op::is_null() const { return prim_op == NUM_OPS_AND_NULL; }

std::pair<std::size_t, std::size_t> get_arity(PrimOp po)
{
  const PrimOpInfo & row = info(po, "get_arity");
  return { row.min_arity, row.max_arity };
}

Theory get_theory(PrimOp po) { return info(po, "get_theory").theory; }

std::uint64_t get_num_indices(PrimOp po)
{
  return info(po, "get_num_indices").num_indices;
}

bool operator==(Op o1, Op o2)
{
  if (o1.prim_op != o2.prim_op)
  {
    return false;
  }
  else if (o1.num_idx != o2.num_idx)
  {
    return false;
  }
  else
  {
    return (o1.num_idx == 0) || ((o1.num_idx == 1) && (o1.idx0 == o2.idx0))
           || ((o1.num_idx == 2) && (o1.idx0 == o2.idx0)
               && (o1.idx1 == o2.idx1));
  }
}

bool operator!=(Op o1, Op o2) { return !(o1 == o2); }

std::ostream & operator<<(std::ostream & output, const Op o)
{
  output << o.to_string();
  return output;
}

bool is_left_assoc(PrimOp po) { return assoc_of(po) == Assoc::LEFT; }

bool is_right_assoc(PrimOp po) { return assoc_of(po) == Assoc::RIGHT; }

bool is_chainable(PrimOp po) { return assoc_of(po) == Assoc::CHAINABLE; }

bool is_pairwise(PrimOp po) { return assoc_of(po) == Assoc::PAIRWISE; }

bool is_variadic(PrimOp po) { return assoc_of(po) != Assoc::NONE; }

}  // namespace smt

namespace std {

size_t hash<smt::Op>::operator()(const smt::Op o) const
{
  // The hash function for op computes the string hash
  hash<string> str_hash;
  return str_hash(o.to_string());
}

}  // namespace std
