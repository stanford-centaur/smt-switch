#ifndef SMT_CVC4_FUN_H
#define SMT_CVC4_FUN_H

#include <unordered_map>

#include "api/cvc4cpp.h"

#include "exceptions.h"
#include "fun.h"
#include "ops.h"
#include "sort.h"

namespace smt {
  // forward declaration
  class CVC4Solver;

  class CVC4Fun : public AbsFun
  {
  public:
    CVC4Fun(::CVC4::api::Term fun) : fun(fun), uf(true), indexed(false) {}
    CVC4Fun(::CVC4::api::Kind kind) : kind(kind), uf(false), indexed(false) {}
    CVC4Fun(::CVC4::api::Kind kind, ::CVC4::api::OpTerm o)
        : kind(kind), op(o), uf(false), indexed(true)
    {
    }
    bool is_uf() const override;
    bool is_op() const override;
    bool is_prim_op() const;
    bool is_indexed() const;
    Sort get_sort() const override;
    Op get_op() const override;
    std::string get_name() const override;
  protected:
    ::CVC4::api::Term fun;
    ::CVC4::api::Kind kind;
    ::CVC4::api::OpTerm op;
    // true if this Fun holds an uninterpreted function (CVC4::api::Term)
    bool uf;
    // only relevant if uf is false, says whether this Fun holds a kind or opterm
    bool indexed;

    friend class CVC4Solver;
  };

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
      { Extract, ::CVC4::api::BITVECTOR_EXTRACT },
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
      {Zero_Extend, ::CVC4::api::BITVECTOR_ZERO_EXTEND},
      // Indexed Op
      {Sign_Extend, ::CVC4::api::BITVECTOR_SIGN_EXTEND},
      // Indexed Op
      {Repeat, ::CVC4::api::BITVECTOR_REPEAT},
      // Indexed Op
      {Rotate_Left, ::CVC4::api::BITVECTOR_ROTATE_LEFT},
      // Indexed Op
      {Rotate_Right, ::CVC4::api::BITVECTOR_ROTATE_RIGHT},
      { Select, ::CVC4::api::SELECT },
      { Store, ::CVC4::api::STORE },
    });

const std::unordered_map<::CVC4::api::Kind, PrimOp> kind2primop(
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
      { ::CVC4::api::BITVECTOR_EXTRACT, Extract },
      { ::CVC4::api::BITVECTOR_NOT, BVNot },
      { ::CVC4::api::BITVECTOR_NEG, BVNeg },
      {  ::CVC4::api::BITVECTOR_AND, BVAnd },
      { ::CVC4::api::BITVECTOR_OR, BVOr },
      { ::CVC4::api::BITVECTOR_XOR, BVXor },
      { ::CVC4::api::BITVECTOR_NAND, BVNand },
      { ::CVC4::api::BITVECTOR_NOR, BVNor },
      { ::CVC4::api::BITVECTOR_XNOR, BVXnor },
      { ::CVC4::api::BITVECTOR_COMP, BVComp },
      {  ::CVC4::api::BITVECTOR_PLUS, BVAdd},
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
      { ::CVC4::api::BITVECTOR_ZERO_EXTEND, Zero_Extend },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_SIGN_EXTEND, Sign_Extend },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_REPEAT, Repeat },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_ROTATE_LEFT, Rotate_Left },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_ROTATE_RIGHT, Rotate_Right },
      { ::CVC4::api::SELECT, Select },
      { ::CVC4::api::STORE, Store }
      });

 // the kinds CVC4 needs to build an OpTerm for an indexed op
 const std::unordered_map<PrimOp, ::CVC4::api::Kind> primop2optermcon(
    { { Extract, ::CVC4::api::BITVECTOR_EXTRACT_OP },
      {Zero_Extend, ::CVC4::api::BITVECTOR_ZERO_EXTEND_OP },
      {Sign_Extend, ::CVC4::api::BITVECTOR_SIGN_EXTEND_OP },
      {Repeat, ::CVC4::api::BITVECTOR_REPEAT_OP },
      {Rotate_Left, ::CVC4::api::BITVECTOR_ROTATE_LEFT_OP },
      {Rotate_Right, ::CVC4::api::BITVECTOR_ROTATE_RIGHT_OP },
    });


}

#endif
