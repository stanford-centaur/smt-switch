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

#pragma once

#include <cstdint>
#include <iostream>
#include <string>
#include <utility>
#include <unordered_set>
#include <functional>

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
  BV_To_Nat,
  Int_To_BV,
  //Strings
  StrLt,
  StrLeq,
  StrLen,
  StrConcat,
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
  Op() : prim_op(NUM_OPS_AND_NULL), num_idx(0){};
  Op(PrimOp o) : prim_op(o), num_idx(0){};
  Op(PrimOp o, uint64_t idx0) : prim_op(o), num_idx(1), idx0(idx0){};
  Op(PrimOp o, uint64_t idx0, uint64_t idx1)
      : prim_op(o), num_idx(2), idx0(idx0), idx1(idx1){};
  std::string to_string() const;
  bool is_null() const;
  PrimOp prim_op;
  uint64_t num_idx;
  uint64_t idx0;
  uint64_t idx1;
};
using UnorderedOpSet = std::unordered_set<Op>;

/** Looks up the expected arity of a PrimOp
 *  @return a tuple with the minimum and maximum
 *          accepted arity (in that order)
 */
std::pair<size_t, size_t> get_arity(PrimOp po);

std::string to_string(PrimOp op);
bool operator==(Op o1, Op o2);
bool operator!=(Op o1, Op o2);
std::ostream& operator<<(std::ostream& output, const Op o);

}  // namespace smt

// defining hash for old compilers
namespace std
{
  // specialize the hash template for PrimOp
  template<>
    struct hash<smt::PrimOp>
    {
      size_t operator()(const smt::PrimOp o) const
      {
        return static_cast<std::size_t>(o);
      }
    };

  // specialize the hash template for Op
  template<>
    struct hash<smt::Op>
    {
      size_t operator()(const smt::Op o) const
      {
        // The hash function for op computes the string hash
        std::hash<std::string> str_hash;
        return str_hash(o.to_string());
      }
    };
}

namespace smt {
// ops that can be applied to n arguments
const std::unordered_set<PrimOp> variadic_ops(
    { And, Or, Xor, Plus, BVAnd, BVOr, BVAdd });

bool is_variadic(PrimOp po);
}  // namespace smt
