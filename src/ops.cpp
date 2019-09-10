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

  primop2str[And] = std::string_view("and");
  primop2str[Or] = std::string_view("or");
  primop2str[Xor] = std::string_view("xor");
  primop2str[Not] = std::string_view("not");
  primop2str[Implies] = std::string_view("=>");
  primop2str[Iff] = std::string_view("<=>");
  primop2str[Ite] = std::string_view("ite");
  primop2str[Equal] = std::string_view("=");
  primop2str[Distinct] = std::string_view("distinct");
  primop2str[Plus] = std::string_view("+");
  primop2str[Minus] = std::string_view("-");
  primop2str[Negate] = std::string_view("-");
  primop2str[Mult] = std::string_view("*");
  primop2str[Div] = std::string_view("div");
  primop2str[Lt] = std::string_view("<");
  primop2str[Le] = std::string_view("<=");
  primop2str[Gt] = std::string_view(">");
  primop2str[Ge] = std::string_view(">=");
  primop2str[Mod] = std::string_view("mod");
  primop2str[Abs] = std::string_view("abs");
  primop2str[Pow] = std::string_view("pow");
  primop2str[Concat] = std::string_view("concat");
  primop2str[Extract] = std::string_view("extract");
  primop2str[BVNot] = std::string_view("bvnot");
  primop2str[BVNeg] = std::string_view("bvneg");
  primop2str[BVAnd] = std::string_view("bvand");
  primop2str[BVOr] = std::string_view("bvor");
  primop2str[BVXor] = std::string_view("bvxor");
  primop2str[BVNand] = std::string_view("bvnand");
  primop2str[BVNor] = std::string_view("bvnor");
  primop2str[BVXnor] = std::string_view("bvxnor");
  primop2str[BVComp] = std::string_view("bvcomp");
  primop2str[BVAdd] = std::string_view("bvadd");
  primop2str[BVSub] = std::string_view("bvsub");
  primop2str[BVMul] = std::string_view("bvmul");
  primop2str[BVUdiv] = std::string_view("bvudiv");
  primop2str[BVSdiv] = std::string_view("bvsdiv");
  primop2str[BVUrem] = std::string_view("bvurem");
  primop2str[BVSrem] = std::string_view("bvsrem");
  primop2str[BVSmod] = std::string_view("bvsmod");
  primop2str[BVShl] = std::string_view("bvshl");
  primop2str[BVAshr] = std::string_view("bvashr");
  primop2str[BVLshr] = std::string_view("bvlshr");
  primop2str[BVUlt] = std::string_view("bvult");
  primop2str[BVUle] = std::string_view("bvule");
  primop2str[BVUgt] = std::string_view("bvugt");
  primop2str[BVUge] = std::string_view("bvuge");
  primop2str[BVSlt] = std::string_view("bvslt");
  primop2str[BVSle] = std::string_view("bvsle");
  primop2str[BVSgt] = std::string_view("bvsgt");
  primop2str[BVSge] = std::string_view("bvsge");
  primop2str[Zero_Extend] = std::string_view("zero_extend");
  primop2str[Sign_Extend] = std::string_view("sign_extend");
  primop2str[Repeat] = std::string_view("repeat");
  primop2str[Rotate_Left] = std::string_view("rotate_left");
  primop2str[Rotate_Right] = std::string_view("rotate_right");
  primop2str[Select] = std::string_view("select");
  primop2str[Store] = std::string_view("store");
  return primop2str;
}

constexpr std::array<std::string_view, NUM_OPS_AND_NULL> primop2str =
    generate_primop2str();

std::string to_string(PrimOp op) { return std::string(primop2str[op]); }

std::string Op::to_string() const
{
  std::string res;
  if (num_idx)
  {
    res += "(_ ";
  }

  res += std::string(primop2str[prim_op]);

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
  output << o.to_string();
  return output;
}

}  // namespace smt
