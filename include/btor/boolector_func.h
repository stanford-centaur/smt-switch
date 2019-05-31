#ifndef SMT_BOOLECTOR_OP_H
#define SMT_BOOLECTOR_OP_H

#include <unordered_map>

#include "func.h"

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
    virtual unsigned int get_upper() const {
      throw IncorrectUsageException("Expecting BoolectorExtractOp.");
    };
    virtual unsigned int get_lower() const {
      throw IncorrectUsageException("Expecting BoolectorExtractOp.");
    };
    virtual unsigned int get_idx() const {
      throw IncorrectUsageException("Expecting Op with single index");
    };

    friend class BoolectorSolver;
  };

  // boolector doesn't have a node type for indexed ops (only functions for performing them)
  // thus we track the information here

  class BoolectorExtractOp : public BoolectorIndexedOp
  {
  public:
    BoolectorExtractOp(PrimOp o, unsigned int u, unsigned int l)
        : BoolectorIndexedOp(o), upper(u), lower(l){};
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
        : BoolectorIndexedOp(o), idx(i){};
    unsigned int get_idx() const override { return idx; };

  protected:
    unsigned int idx;

    friend class BoolectorSolver;
  };

  // Boolector PrimOp mappings
  typedef BoolectorNode *(*un_fun)(Btor *, BoolectorNode *);
  typedef BoolectorNode *(*bin_fun)(Btor *, BoolectorNode *, BoolectorNode *);
  typedef BoolectorNode *(*tern_fun)(Btor *, BoolectorNode *, BoolectorNode *,
                                     BoolectorNode *);

  const std::unordered_map<PrimOp, un_fun> unary_ops({{Not, boolector_not},
                                                      {BVNot, boolector_not},
                                                      {BVNeg, boolector_neg}});

  const std::unordered_map<PrimOp, bin_fun>
      binary_ops({{And, boolector_and},     {Or, boolector_or},
                  {Xor, boolector_xor},     {Implies, boolector_implies},
                  {Iff, boolector_iff},     {Equal, boolector_eq},
                  {BVAnd, boolector_and},   {BVOr, boolector_or},
                  {BVXor, boolector_xor},   {BVAdd, boolector_add},
                  {BVSub, boolector_sub},   {BVMul, boolector_mul},
                  {BVUrem, boolector_urem}, {BVSrem, boolector_srem},
                  {BVMod, boolector_smod},  {BVAshr, boolector_sra},
                  {BVLshr, boolector_srl},  {BVShl, boolector_sll},
                  {BVUlt, boolector_ult},   {BVUle, boolector_ulte},
                  {BVUgt, boolector_ugt},   {BVUge, boolector_ugte},
                  {BVSlt, boolector_slt},   {BVSle, boolector_slte},
                  {BVSgt, boolector_sgt},   {BVSge, boolector_sgte},
                  {Select, boolector_read}});

  const std::unordered_map<PrimOp, tern_fun>
      ternary_ops({{Ite, boolector_cond}, {Store, boolector_write}});
}

#endif
