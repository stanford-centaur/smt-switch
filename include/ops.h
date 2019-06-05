#ifndef SMT_OPS_H
#define SMT_OPS_H

#include <array>
#include <iostream>
#include <string>

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
  Iff,
  Ite,
  Equal,
  Distinct,
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
  BVComp,
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
  /* Array Theory */
  Select,
  Store,
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
  explicit Op(PrimOp o) : prim_op(o), num_idx(0){};
  Op(PrimOp o, unsigned int idx0) : prim_op(o), num_idx(1), idx0(idx0){};
  Op(PrimOp o, unsigned int idx0, unsigned int idx1)
      : prim_op(o), num_idx(2), idx0(idx0), idx1(idx1){};
  PrimOp prim_op;
  unsigned int num_idx;
  unsigned int idx0;
  unsigned int idx1;
};

/**
   This function should only be called once, to generate the constexpr
   primop2str for converting enums to string_views.
*/
constexpr std::array<std::string_view, NUM_OPS_AND_NULL> generate_primop2str()
{
  std::array<std::string_view, NUM_OPS_AND_NULL> primop2str;

  primop2str[And] = std::string_view("And");
  primop2str[Or] = std::string_view("Or");
  primop2str[Xor] = std::string_view("Xor");
  primop2str[Not] = std::string_view("Not");
  primop2str[Implies] = std::string_view("Implies");
  primop2str[Iff] = std::string_view("Iff");
  primop2str[Ite] = std::string_view("Ite");
  primop2str[Equal] = std::string_view("Equal");
  primop2str[Distinct] = std::string_view("Distinct");
  primop2str[Concat] = std::string_view("Concat");
  primop2str[Extract] = std::string_view("Extract");
  primop2str[BVNot] = std::string_view("BVNot");
  primop2str[BVNeg] = std::string_view("BVNeg");
  primop2str[BVAnd] = std::string_view("BVAnd");
  primop2str[BVOr] = std::string_view("BVOr");
  primop2str[BVXor] = std::string_view("BVXor");
  primop2str[BVNand] = std::string_view("BVNand");
  primop2str[BVNor] = std::string_view("BVNor");
  primop2str[BVXnor] = std::string_view("BVXnor");
  primop2str[BVComp] = std::string_view("BVComp");
  primop2str[BVAdd] = std::string_view("BVAdd");
  primop2str[BVSub] = std::string_view("BVSub");
  primop2str[BVMul] = std::string_view("BVMul");
  primop2str[BVUdiv] = std::string_view("BVUdiv");
  primop2str[BVSdiv] = std::string_view("BVSdiv");
  primop2str[BVUrem] = std::string_view("BVUrem");
  primop2str[BVSrem] = std::string_view("BVSrem");
  primop2str[BVSmod] = std::string_view("BVSmod");
  primop2str[BVShl] = std::string_view("BVShl");
  primop2str[BVAshr] = std::string_view("BVAshr");
  primop2str[BVLshr] = std::string_view("BVLshr");
  primop2str[BVUlt] = std::string_view("BVUlt");
  primop2str[BVUle] = std::string_view("BVUle");
  primop2str[BVUgt] = std::string_view("BVUgt");
  primop2str[BVUge] = std::string_view("BVUge");
  primop2str[BVSlt] = std::string_view("BVSlt");
  primop2str[BVSle] = std::string_view("BVSle");
  primop2str[BVSgt] = std::string_view("BVSgt");
  primop2str[BVSge] = std::string_view("BVSge");
  primop2str[Zero_Extend] = std::string_view("Zero_Extend");
  primop2str[Sign_Extend] = std::string_view("Sign_Extend");
  primop2str[Repeat] = std::string_view("Repeat");
  primop2str[Rotate_Left] = std::string_view("Rotate_Left");
  primop2str[Rotate_Right] = std::string_view("Rotate_Right");
  primop2str[Select] = std::string_view("Select");
  primop2str[Store] = std::string_view("Store");
  return primop2str;
}

constexpr std::array<std::string_view, NUM_OPS_AND_NULL> primop2str =
    generate_primop2str();

std::string to_string(PrimOp op) { return std::string(primop2str[op]); }

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

bool operator!=(Op o1, Op o2)
{
  if (o1.prim_op != o2.prim_op)
  {
    return true;
  }
  else if (o1.num_idx != o2.num_idx)
  {
    return true;
  }
  else
  {
    return ((o1.num_idx > 1) || (o1.idx0 != o2.idx0))
           && ((o1.num_idx != 2) || (o1.idx0 != o2.idx0)
               || (o1.idx1 != o2.idx1));
  }
}

std::ostream& operator<<(std::ostream& output, const Op o)
{
 output << "(" << ::smt::to_string(o.prim_op);
 if (o.num_idx > 0)
 {
   output << " " << o.idx0;
  }
 if (o.num_idx == 2)
 {
   output << " " << o.idx1;
 }
 output << ")";
 return output;
}

}  // namespace smt

#endif
