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

#include <string>
#include <unordered_map>

#include "ops.h"

namespace smt {

const std::unordered_map<PrimOp, std::string> primop2str(
    { { And, "and" },
      { Or, "or" },
      { Xor, "xor" },
      { Not, "not" },
      { Implies, "=>" },
      { Iff, "<=>" },
      { Ite, "ite" },
      { Equal, "=" },
      { Distinct, "distinct" },
      { Apply, "apply" },
      { Plus, "+" },
      { Minus, "-" },
      { Negate, "-" },
      { Mult, "*" },
      { Div, "/" },
      { IntDiv, "div" },
      { Lt, "<" },
      { Le, "<=" },
      { Gt, ">" },
      { Ge, ">=" },
      { Mod, "mod" },
      { Abs, "abs" },
      { Pow, "pow" },
      { Concat, "concat" },
      { Extract, "extract" },
      { BVNot, "bvnot" },
      { BVNeg, "bvneg" },
      { BVAnd, "bvand" },
      { BVOr, "bvor" },
      { BVXor, "bvxor" },
      { BVNand, "bvnand" },
      { BVNor, "bvnor" },
      { BVXnor, "bvxnor" },
      { BVComp, "bvcomp" },
      { BVAdd, "bvadd" },
      { BVSub, "bvsub" },
      { BVMul, "bvmul" },
      { BVUdiv, "bvudiv" },
      { BVSdiv, "bvsdiv" },
      { BVUrem, "bvurem" },
      { BVSrem, "bvsrem" },
      { BVSmod, "bvsmod" },
      { BVShl, "bvshl" },
      { BVAshr, "bvashr" },
      { BVLshr, "bvlshr" },
      { BVUlt, "bvult" },
      { BVUle, "bvule" },
      { BVUgt, "bvugt" },
      { BVUge, "bvuge" },
      { BVSlt, "bvslt" },
      { BVSle, "bvsle" },
      { BVSgt, "bvsgt" },
      { BVSge, "bvsge" },
      { Zero_Extend, "zero_extend" },
      { Sign_Extend, "sign_extend" },
      { Repeat, "repeat" },
      { Rotate_Left, "rotate_left" },
      { Rotate_Right, "rotate_right" },
      { Select, "select" },
      { Store, "store" },
      { Apply_Selector, "apply_selector"},
      { Apply_Tester, "apply_tester"},
      { Apply_Constructor, "apply_constructor"}  });

std::string to_string(PrimOp op)
{
  if (op == NUM_OPS_AND_NULL)
  {
    return "null";
  }

  return primop2str.at(op);
}

std::string Op::to_string() const
{
  std::string res;
  if (num_idx)
  {
    res += "(_ ";
  }

  res += ::smt::to_string(prim_op);

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

bool Op::is_null() const
{
  return prim_op == NUM_OPS_AND_NULL;
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

}  // namespace smt
