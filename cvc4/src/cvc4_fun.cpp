#include <unordered_map>

#include "cvc4_fun.h"

namespace
{

const std::unordered_map<PrimOp, ::CVC4::api::Kind> primop2kind(
    { { And, ::CVC4::api::AND },
      { Or, ::CVC4::api::OR },
      { Xor, ::CVC4::api::XOR },
      { Not, ::CVC4::api::NOT },
      { Implies, ::CVC4::api::IMPLIES },
      { Ite, ::CVC4::api::ITE },
      { Iff, ::CVC4::api::EQUAL },
      { Equal, ::CVC4::api::EQUAL },
      { Distinct, ::CVC4::api::DISTINCT },
      { Concat, ::CVC4::api::BITVECTOR_CONCAT },
      // Indexed Op
      { Extract, ::CVC4::api::BITVECTOR_EXTRACT_OP },
      { BVNot, ::CVC4::api::BITVECTOR_NOT },
      { BVNeg, ::CVC4::api::BITVECTOR_NEG },
      { BVAnd,  ::CVC4::api::BITVECTOR_AND },
      { BVOr, ::CVC4::api::BITVECTOR_OR },
      { BVXor, ::CVC4::api::BITVECTOR_XOR },
      { BVNand, ::CVC4::api::BITVECTOR_NAND },
      { BVNor, ::CVC4::api::BITVECTOR_NOR },
      { BVXnor, ::CVC4::api::BITVECTOR_XNOR },
      { BVComp, ::CVC4::api::BITVECTOR_COMP },
      { BVAdd,  ::CVC4::api::BITVECTOR_PLUS},
      { BVSub, ::CVC4::api::BITVECTOR_SUB },
      { BVMul, ::CVC4::api::BITVECTOR_MULT },
      { BVUdiv, ::CVC4::api::BITVECTOR_UDIV },
      { BVSdiv, ::CVC4::api::BITVECTOR_SDIV },
      { BVUrem, ::CVC4::api::BITVECTOR_UREM },
      { BVSrem, ::CVC4::api::BITVECTOR_SREM },
      { BVSmod, ::CVC4::api::BITVECTOR_SMOD },
      { BVShl, ::CVC4::api::BITVECTOR_SHL },
      { BVAshr, ::CVC4::api::BITVECTOR_ASHR },
      { BVLshr, ::CVC4::api::BITVECTOR_LSHR },
      { BVUlt, ::CVC4::api::BITVECTOR_ULT },
      { BVUle, ::CVC4::api::BITVECTOR_ULE },
      { BVUgt, ::CVC4::api::BITVECTOR_UGT },
      { BVUge, ::CVC4::api::BITVECTOR_UGE },
      { BVSlt, ::CVC4::api::BITVECTOR_SLT },
      { BVSle, ::CVC4::api::BITVECTOR_SLE },
      { BVSgt, ::CVC4::api::BITVECTOR_SGT },
      { BVSge, ::CVC4::api::BITVECTOR_SGE },
      // Indexed Op
      {Zero_Extend, ::CVC4::api::BITVECTOR_ZERO_EXTEND_OP},
      // Indexed Op
      {Sign_Extend, ::CVC4::api::BITVECTOR_SIGN_EXTEND_OP},
      // Indexed Op
      {Repeat, ::CVC4::api::BITVECTOR_REPEAT_OP},
      // Indexed Op
      {Rotate_Left, ::CVC4::api::BITVECTOR_ROTATE_LEFT_OP},
      // Indexed Op
      {Rotate_Right, ::CVC4::api::BITVECTOR_ROTATE_RIGHT_OP},
      { Select, ::CVC4::api::SELECT },
      { Store, ::CVC4::api::STORE },
    });

const std::unordered_map<PrimOp, ::CVC4::api::Kind> kind2primop(
    { { ::CVC4::api::AND, And },
      { ::CVC4::api::OR, Or },
      { ::CVC4::api::XOR, Xor },
      { ::CVC4::api::NOT, Not },
      { ::CVC4::api::IMPLIES, Implies },
      { ::CVC4::api::ITE, Ite },
      { ::CVC4::api::EQUAL, Iff },
      { ::CVC4::api::EQUAL, Equal },
      { ::CVC4::api::DISTINCT, Distinct },
      { ::CVC4::api::BITVECTOR_CONCAT, Concat },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_EXTRACT_OP, Extract },
      { ::CVC4::api::BITVECTOR_NOT, BVNot },
      { ::CVC4::api::BITVECTOR_NEG, BVNeg },
      {  ::CVC4::api::BITVECTOR_AND, BVAnd },
      { ::CVC4::api::BITVECTOR_OR, BVOr },
      { ::CVC4::api::BITVECTOR_XOR, BVXor },
      { ::CVC4::api::BITVECTOR_NAND, BVNand },
      { ::CVC4::api::BITVECTOR_NOR, BVNor },
      { ::CVC4::api::BITVECTOR_XNOR, BVXnor },
      { ::CVC4::api::BITVECTOR_COMP, BVComp },
      {  ::CVC4::api::BITVECTOR_PLU, BVAddS},
      { ::CVC4::api::BITVECTOR_SUB, BVSub },
      { ::CVC4::api::BITVECTOR_MULT, BVMul },
      { ::CVC4::api::BITVECTOR_UDIV, BVUdiv },
      { ::CVC4::api::BITVECTOR_SDIV, BVSdiv },
      { ::CVC4::api::BITVECTOR_UREM, BVUrem },
      { ::CVC4::api::BITVECTOR_SREM, BVSrem },
      { ::CVC4::api::BITVECTOR_SMOD, BVSmod },
      { ::CVC4::api::BITVECTOR_SHL, BVShl },
      { ::CVC4::api::BITVECTOR_ASHR, BVAshr },
      { ::CVC4::api::BITVECTOR_LSHR, BVLshr },
      { ::CVC4::api::BITVECTOR_ULT, BVUlt },
      { ::CVC4::api::BITVECTOR_ULE, BVUle },
      { ::CVC4::api::BITVECTOR_UGT, BVUgt },
      { ::CVC4::api::BITVECTOR_UGE, BVUge },
      { ::CVC4::api::BITVECTOR_SLT, BVSlt },
      { ::CVC4::api::BITVECTOR_SLE, BVSle },
      { ::CVC4::api::BITVECTOR_SGT, BVSgt },
      { ::CVC4::api::BITVECTOR_SGE, BVSge },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_ZERO_EXTEND_OP, Zero_Extend },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_SIGN_EXTEND_OP, Sign_Extend },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_REPEAT_OP, Repeat },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_ROTATE_LEFT_OP, Rotate_Left },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_ROTATE_RIGHT_OP, Rotate_Right },
      { ::CVC4::api::SELECT, Select },
      { ::CVC4::api::STORE, Store },
    });


}

namespace smt {

bool CVC4Fun::is_uf() const {
  return is_uf;
}

bool CVC4Fun::is_op() const {
  return !is_uf;
}

Sort CVC4Fun::get_sort() const
{
  if (!is_uf)
    {
      throw IncorrectUsageException("Can't get sort for builtin operator.");
    }
  ::CVC4::api::Sort cs = fun.getSort();
  Sort s(new CVC4Sort(cs));
  return s;
}

Op CVC4Fun::get_op() const
{
  if (is_uf) {
    throw IncorrectUsageException("Can't get op from uninterpretd function.");
  }
  if (!indexed)
  {
    return Op(kind2primop[kind]);
  }
  else
  {
    PrimOp o = kind2primop[kind];
    if (o == Extract)
    {
      std::string rep = op.toString();
      std::string indices = rep.erase(0, rep.find(" ") + 1);
      indices = indices.erase(0, indices.find(" ") + 1);
      indices = indices.substr(0, indices.length()-1);
      std::size_t pos = indices.find(" ");
      std::string idx0 = indices.substr(0, pos);
      std::string idx1 = indices.substr(pos+1, idx1.length() - pos);
      return Op(Extract, std::atoi(idx0.c_str()), std::atoi(idx1.c_str()));
    }
    else
    {
      // TODO: Implement these
      throw NotImplementedException("Other indexed operators currently unimplemented.");
    }
  }
}

std::string CVC4Fun::get_name() const
{
  if (!is_uf)
    {
      throw IncorrectUsageException("Can't get name of builtin operator.");
    }
  return fun.toString();
}

}
