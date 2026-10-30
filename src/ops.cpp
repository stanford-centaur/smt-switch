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
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#include "exceptions.h"

namespace smt {

// a map from PrimOp to <minimum arity, maximum arity>
const std::unordered_map<PrimOp, std::pair<std::size_t, std::size_t>>
    primop2arity({
        { And, { 2, INT_MAX } },
        { Or, { 2, INT_MAX } },
        { Xor, { 2, INT_MAX } },
        { Not, { 1, 1 } },
        { Implies, { 2, INT_MAX } },
        { Ite, { 3, 3 } },
        { Equal, { 2, INT_MAX } },
        { Distinct, { 2, INT_MAX } },
        // at least the function and one argument
        // of course, to be well-sorted the number of arguments must
        // match the function domain
        { Apply, { 2, INT_MAX } },
        { Plus, { 2, INT_MAX } },
        { Minus, { 2, INT_MAX } },
        { Negate, { 1, 1 } },
        { Mult, { 2, INT_MAX } },
        { Div, { 2, INT_MAX } },
        { IntDiv, { 2, INT_MAX } },
        { To_Real, { 1, 1 } },
        { To_Int, { 1, 1 } },
        { Is_Int, { 1, 1 } },
        { Lt, { 2, INT_MAX } },
        { Le, { 2, INT_MAX } },
        { Gt, { 2, INT_MAX } },
        { Ge, { 2, INT_MAX } },
        { Mod, { 2, 2 } },
        { Abs, { 1, 1 } },
        { Pow, { 2, 2 } },
        { Concat, { 2, 2 } },
        { Extract, { 1, 1 } },
        { BVNot, { 1, 1 } },
        { BVNeg, { 1, 1 } },
        { BVAnd, { 2, INT_MAX } },
        { BVOr, { 2, INT_MAX } },
        { BVXor, { 2, INT_MAX } },
        { BVNand, { 2, 2 } },
        { BVNor, { 2, 2 } },
        { BVXnor, { 2, 2 } },
        { BVComp, { 2, 2 } },
        { BVAdd, { 2, INT_MAX } },
        { BVSub, { 2, 2 } },
        { BVMul, { 2, INT_MAX } },
        { BVUdiv, { 2, 2 } },
        { BVSdiv, { 2, 2 } },
        { BVUrem, { 2, 2 } },
        { BVSrem, { 2, 2 } },
        { BVSmod, { 2, 2 } },
        { BVShl, { 2, 2 } },
        { BVAshr, { 2, 2 } },
        { BVLshr, { 2, 2 } },
        { BVUlt, { 2, 2 } },
        { BVUle, { 2, 2 } },
        { BVUgt, { 2, 2 } },
        { BVUge, { 2, 2 } },
        { BVSlt, { 2, 2 } },
        { BVSle, { 2, 2 } },
        { BVSgt, { 2, 2 } },
        { BVSge, { 2, 2 } },
        { Zero_Extend, { 1, 1 } },
        { Sign_Extend, { 1, 1 } },
        { Repeat, { 1, 1 } },
        { Rotate_Left, { 1, 1 } },
        { Rotate_Right, { 1, 1 } },
        { BV_To_Nat, { 1, 1 } },
        { UBV_To_Int, { 1, 1 } },
        { SBV_To_Int, { 1, 1 } },
        { Int_To_BV, { 1, 1 } },
        { StrLt, { 2, INT_MAX } },
        { StrLeq, { 2, INT_MAX } },
        { StrLen, { 1, 1 } },
        { StrConcat, { 2, INT_MAX } },
        { StrSubstr, { 3, 3 } },
        { StrAt, { 2, 2 } },
        { StrContains, { 2, 2 } },
        { StrIndexof, { 3, 3 } },
        { StrReplace, { 3, 3 } },
        { StrReplaceAll, { 3, 3 } },
        { StrPrefixof, { 2, 2 } },
        { StrSuffixof, { 2, 2 } },
        { StrIsDigit, { 1, 1 } },
        { Select, { 2, 2 } },
        { Store, { 3, 3 } },
        // to make term traversal easier considering the differences
        // in the underlying solver's handling of quantifiers, smt-switch
        // always uses the form <Forall/Exists> bound_param . body
        // i.e. it takes two arguments, the parameter to bind and the body
        { Forall, { 2, 2 } },
        { Exists, { 2, 2 } },
        { Apply_Selector, { 2, 2 } },
        { Apply_Tester, { 2, 2 } },
        // a nullary constructor is applied to nothing but itself
        { Apply_Constructor, { 1, INT_MAX } },
    });

std::string to_string(PrimOp op)
{
  switch (op)
  {
    case And: return "and";
    case Or: return "or";
    case Xor: return "xor";
    case Not: return "not";
    case Implies: return "=>";
    case Ite: return "ite";
    case Equal: return "=";
    case Distinct: return "distinct";
    case Apply: return "apply";
    case Plus: return "+";
    case Minus:
    case Negate: return "-";
    case Mult: return "*";
    case Div: return "/";
    case IntDiv: return "div";
    case To_Real: return "to_real";
    case To_Int: return "to_int";
    case Is_Int: return "is_int";
    case Lt: return "<";
    case Le: return "<=";
    case Gt: return ">";
    case Ge: return ">=";
    case Mod: return "mod";
    case Abs: return "abs";
    case Pow: return "pow";
    case Concat: return "concat";
    case Extract: return "extract";
    case BVNot: return "bvnot";
    case BVNeg: return "bvneg";
    case BVAnd: return "bvand";
    case BVOr: return "bvor";
    case BVXor: return "bvxor";
    case BVNand: return "bvnand";
    case BVNor: return "bvnor";
    case BVXnor: return "bvxnor";
    case BVComp: return "bvcomp";
    case BVAdd: return "bvadd";
    case BVSub: return "bvsub";
    case BVMul: return "bvmul";
    case BVUdiv: return "bvudiv";
    case BVSdiv: return "bvsdiv";
    case BVUrem: return "bvurem";
    case BVSrem: return "bvsrem";
    case BVSmod: return "bvsmod";
    case BVShl: return "bvshl";
    case BVAshr: return "bvashr";
    case BVLshr: return "bvlshr";
    case BVUlt: return "bvult";
    case BVUle: return "bvule";
    case BVUgt: return "bvugt";
    case BVUge: return "bvuge";
    case BVSlt: return "bvslt";
    case BVSle: return "bvsle";
    case BVSgt: return "bvsgt";
    case BVSge: return "bvsge";
    case Zero_Extend: return "zero_extend";
    case Sign_Extend: return "sign_extend";
    case Repeat: return "repeat";
    case Rotate_Left: return "rotate_left";
    case Rotate_Right: return "rotate_right";
    case BV_To_Nat:
    case UBV_To_Int: return "ubv_to_int";
    case SBV_To_Int: return "sbv_to_int";
    case Int_To_BV: return "int_to_bv";
    case StrLt: return "str.<";
    case StrLeq: return "str.<=";
    case StrLen: return "str.len";
    case StrConcat: return "str.++";
    case StrSubstr: return "str.substr";
    case StrAt: return "str.at";
    case StrContains: return "str.contains";
    case StrIndexof: return "str.indexof";
    case StrReplace: return "str.replace";
    case StrReplaceAll: return "str.replace_all";
    case StrPrefixof: return "str.prefixof";
    case StrSuffixof: return "str.suffixof";
    case StrIsDigit: return "str.is_digit";
    case Select: return "select";
    case Store: return "store";
    case Forall: return "forall";
    case Exists: return "exists";
    case Apply_Selector: return "apply_selector";
    case Apply_Tester: return "apply_tester";
    case Apply_Constructor: return "apply_constructor";
    case NUM_OPS_AND_NULL: return "null";
  }
  throw SmtException("to_string got an out-of-range PrimOp "
                     + std::to_string(static_cast<int>(op)));
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
  return primop2arity.at(po);
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

const std::unordered_set<PrimOp> left_assoc_ops({ And,
                                                  Or,
                                                  Xor,
                                                  Plus,
                                                  Minus,
                                                  Mult,
                                                  Div,
                                                  IntDiv,
                                                  BVAnd,
                                                  BVOr,
                                                  BVXor,
                                                  BVAdd,
                                                  BVMul,
                                                  StrConcat });
const std::unordered_set<PrimOp> right_assoc_ops({ Implies });
const std::unordered_set<PrimOp> chainable_ops(
    { Equal, Lt, Le, Gt, Ge, StrLt, StrLeq });
const std::unordered_set<PrimOp> pairwise_ops({ Distinct });

bool is_left_assoc(PrimOp po)
{
  return left_assoc_ops.find(po) != left_assoc_ops.end();
}

bool is_right_assoc(PrimOp po)
{
  return right_assoc_ops.find(po) != right_assoc_ops.end();
}

bool is_chainable(PrimOp po)
{
  return chainable_ops.find(po) != chainable_ops.end();
}

bool is_pairwise(PrimOp po)
{
  return pairwise_ops.find(po) != pairwise_ops.end();
}

bool is_variadic(PrimOp po)
{
  return is_left_assoc(po) || is_right_assoc(po) || is_chainable(po)
         || is_pairwise(po);
}

}  // namespace smt

namespace std {

size_t hash<smt::Op>::operator()(const smt::Op o) const
{
  // The hash function for op computes the string hash
  hash<string> str_hash;
  return str_hash(o.to_string());
}

}  // namespace std
