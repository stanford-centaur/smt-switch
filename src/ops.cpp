#include <array>

#include "ops.h"

namespace smt {

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
  primop2str[Plus] = std::string_view("Plus");
  primop2str[Minus] = std::string_view("Minus");
  primop2str[Negate] = std::string_view("Negate");
  primop2str[Mult] = std::string_view("Mult");
  primop2str[Div] = std::string_view("Div");
  primop2str[Lt] = std::string_view("Lt");
  primop2str[Le] = std::string_view("Le");
  primop2str[Gt] = std::string_view("Gt");
  primop2str[Ge] = std::string_view("Ge");
  primop2str[Mod] = std::string_view("Mod");
  primop2str[Abs] = std::string_view("Abs");
  primop2str[Pow] = std::string_view("Pow");
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

std::ostream & operator<<(std::ostream & output, const Op o)
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
