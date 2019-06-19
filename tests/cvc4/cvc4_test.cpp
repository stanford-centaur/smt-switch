#include <iostream>
#include <unordered_map>

#include "smt.h"

#include "api/cvc4cpp.h"

#include "cvc4_term.h"

using namespace std;

using namespace smt;

int main()
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

  ::CVC4::api::Solver slv;
  ::CVC4::api::Term x = slv.mkVar(slv.mkBitVectorSort(8), "x");
  ::CVC4::api::Term y = slv.mkVar(slv.mkBitVectorSort(8), "y");
  CVC4Term x1(x);
  CVC4Term y1(y);
  CVC4Term t(slv.mkTerm(primop2kind.at(BVAdd), x, y));
  cout << t.to_string() << endl;
  cout << t.get_sort() << endl;
  return 0;
}
