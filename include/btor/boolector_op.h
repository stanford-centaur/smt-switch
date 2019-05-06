#ifndef SMT_BOOLECTOR_OP_H
#define SMT_BOOLECTOR_OP_H

#include <unordered_map>

#include "op.h"

#include "boolector/boolector.h"

namespace smt
{
  // forward declaration
  class BoolectorSolver;

  class BoolectorIndexedOp : public AbsIndexedOp
  {
  public:
    BoolectorIndexedOp(PrimOp o) : AbsIndexedOp(o) {};
    virtual bool is_extract_op() const { return false; };
    virtual unsigned int get_upper() const { throw IncorrectUsageException("Expecting BoolectorExtractOp."); };
    virtual unsigned int get_lower() const { throw IncorrectUsageException("Expecting BoolectorExtractOp."); };
    virtual unsigned int get_idx() const { throw IncorrectUsageException("Expecting Op with single index"); };

    friend class BoolectorSolver;
  };

  // boolector doesn't have a node type for indexed ops (only functions for performing them)
  // thus we track the information here

  class BoolectorExtractOp : public BoolectorIndexedOp
  {
  public:
    BoolectorExtractOp(PrimOp o, unsigned int u, unsigned int l)
      : BoolectorIndexedOp(o), upper(u), lower(l) {};
    bool is_extract_op() const override { return true; };
    unsigned int get_upper() const override { return upper; };
    unsigned int get_lower() const override { return lower; };
  protected:
    unsigned int upper;
    unsigned int lower;

    friend class BoolectorSolver;
  };

  class BoolectorSingleIndexOp : public BoolectorIndexedOp
  {
  public:
  BoolectorSingleIndexOp(PrimOp o, unsigned int i)
    : BoolectorIndexedOp(o), idx(i) {};
    unsigned int get_idx() const override { return idx; };
  protected:
    unsigned int idx;

    friend class BoolectorSolver;
  };

  // Boolector PrimOp mappings
  typedef BoolectorNode* (*un_fun)(Btor*, BoolectorNode*);
  typedef BoolectorNode* (*bin_fun)(Btor*, BoolectorNode*, BoolectorNode*);
  typedef BoolectorNode* (*tern_fun)(Btor*, BoolectorNode*, BoolectorNode*, BoolectorNode*);

  const std::unordered_map<PrimOp, un_fun> unary_ops ({
      {NOT, boolector_not},
      {BVNOT, boolector_not},
      {BVNEG, boolector_neg}
    });

  const std::unordered_map<PrimOp, bin_fun> binary_ops({
                          {AND, boolector_and},
                          {OR, boolector_or},
                          {XOR, boolector_xor},
                          {IMPLIES, boolector_implies},
                          {IFF, boolector_iff},
                          {BVAND, boolector_and},
                          {BVOR, boolector_or},
                          {BVXOR, boolector_xor},
                          {BVADD, boolector_add},
                          {BVSUB, boolector_sub},
                          {BVMUL, boolector_mul},
                          {BVUREM, boolector_urem},
                          {BVSREM, boolector_srem},
                          {BVMOD, boolector_smod},
                          {BVASHR, boolector_sra},
                          {BVLSHR, boolector_srl},
                          {BVSHL, boolector_sll},
                          {BVULT, boolector_ult},
                          {BVULE, boolector_ulte},
                          {BVUGT, boolector_ugt},
                          {BVUGE, boolector_ugte},
                          {BVSLT, boolector_slt},
                          {BVSLE, boolector_slte},
                          {BVSGT, boolector_sgt},
                          {BVSGE, boolector_sgte},
                          {SELECT, boolector_read}
    });

  const std::unordered_map<PrimOp, tern_fun> ternary_ops ({
      {ITE, boolector_cond},
      {STORE, boolector_write}
    });

}

#endif
