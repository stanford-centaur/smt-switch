/*********************                                                        */
/*! \file ops.h
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

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#pragma once

#include <cstddef>
#include <cstdint>
#include <ostream>
#include <string>
#include <unordered_set>
#include <utility>

namespace smt {

// Primitive SMT operations (and identifiers for building indexed operators)
// TODO add more smt ops
enum PrimOp
{
  /* Core Theory */
  And = 0,
  Or,
  Xor,
  Not,
  Implies,
  Ite,
  Equal,
  Distinct,
  /* Uninterpreted Functions */
  Apply,
  /* Arithmetic Theories */
  Plus,
  Minus,
  Negate,
  Mult,
  Div,
  Lt,
  Le,
  Gt,
  Ge,
  // Integers only
  Mod,
  Abs,
  Pow,
  IntDiv,
  // Int/Real Conversion and Queries
  To_Real,
  To_Int,
  Is_Int,
  /* Fixed Size BitVector Theory */
  Concat,
  Extract,
  BVNot,
  BVNeg,
  BVAnd,
  BVOr,
  BVXor,
  BVNand,
  BVNor,
  BVXnor,
  BVAdd,
  BVSub,
  BVMul,
  BVUdiv,
  BVSdiv,
  BVUrem,
  BVSrem,
  BVSmod,
  BVShl,
  BVAshr,
  BVLshr,
  BVComp,
  BVUlt,
  BVUle,
  BVUgt,
  BVUge,
  BVSlt,
  BVSle,
  BVSgt,
  BVSge,
  Zero_Extend,
  Sign_Extend,
  Repeat,
  Rotate_Left,
  Rotate_Right,
  // BitVector Conversion
  BV_To_Nat,  // deprecated alias to UBV_To_Int
  UBV_To_Int,
  SBV_To_Int,
  Int_To_BV,
  // Strings
  StrLt,
  StrLeq,
  StrLen,
  StrConcat,
  StrSubstr,
  StrAt,
  StrContains,
  StrIndexof,
  StrReplace,
  StrReplaceAll,
  StrPrefixof,
  StrSuffixof,
  StrIsDigit,
  /* Array Theory */
  Select,
  Store,
  /* Quantifiers */
  // quantifiers can be applied to n arguments where the first n-1
  // are parameters and the nth is a body which uses the parameters
  // binds all the parameters from left to right, i.e. so the resulting
  // term read left to right matches the vector order
  Forall,
  Exists,
  /* Datatype Theory */
  Apply_Selector,
  Apply_Tester,
  Apply_Constructor,
  // TODO if adding new operator, also add to Python bindings in enums_dec.pxi
  // and enums_imp.pxi
  /**
     Serves as both the number of ops and a null element for builtin operators.
   */
  NUM_OPS_AND_NULL
};

/**
   Represents operators
   If num_idx > 0 then it's an indexed operator
 */
struct Op
{
  Op() = default;
  Op(PrimOp o);
  Op(PrimOp o, std::uint64_t index0);
  Op(PrimOp o, std::uint64_t index0, std::uint64_t index1);
  std::string to_string() const;
  bool is_null() const;
  PrimOp prim_op = NUM_OPS_AND_NULL;
  std::uint64_t num_idx = 0;
  // Zeroed so that the constructors leaving one or both unset still produce a
  // readable Op: the public Python properties read them without consulting
  // num_idx.
  std::uint64_t idx0 = 0;
  std::uint64_t idx1 = 0;
};
using UnorderedOpSet = std::unordered_set<Op>;

/** Looks up the expected arity of a PrimOp
 *  @return a tuple with the minimum and maximum
 *          accepted arity (in that order)
 */
std::pair<std::size_t, std::size_t> get_arity(PrimOp po);

std::string to_string(PrimOp op);
bool operator==(Op o1, Op o2);
bool operator!=(Op o1, Op o2);
std::ostream & operator<<(std::ostream & output, const Op o);

}  // namespace smt

namespace std {
template <>
struct hash<smt::Op>
{
  size_t operator()(const smt::Op o) const;
};
}  // namespace std

namespace smt {
/* SMT-LIB defines the applications of some operators to more than two
 * arguments in terms of their applications to two, by giving them one of the
 * attributes below. Every backend takes these operators with any number of
 * arguments, and builds the applications to two itself where its solver
 * takes no more.
 */

/** Whether po is :left-assoc, e.g. (- a b c) is (- (- a b) c) */
bool is_left_assoc(PrimOp po);
/** Whether po is :right-assoc, e.g. (=> a b c) is (=> a (=> b c)) */
bool is_right_assoc(PrimOp po);
/** Whether po is :chainable, e.g. (< a b c) is (and (< a b) (< b c)) */
bool is_chainable(PrimOp po);
/** Whether po is :pairwise, e.g. (distinct a b c) is
 *  (and (distinct a b) (distinct a c) (distinct b c))
 */
bool is_pairwise(PrimOp po);

/** Whether po can be applied to more than two arguments: whether it is
 *  :left-assoc, :right-assoc, :chainable or :pairwise
 */
bool is_variadic(PrimOp po);
}  // namespace smt
