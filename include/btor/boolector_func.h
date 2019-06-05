#ifndef SMT_BOOLECTOR_OP_H
#define SMT_BOOLECTOR_OP_H

#include <unordered_map>

#include "exceptions.h"
#include "func.h"
#include "ops.h"

#include "boolector/boolector.h"

namespace smt {
// forward declaration
class BoolectorSolver;

class BoolectorFunc : public AbsFunc
{
 public:
  BoolectorFunc(Op op) : op(op), contains_op(true){};
  BoolectorFunc(Btor* b, BoolectorNode* n, Sort s)
      : btor(b), node(n), sort(s), contains_op(false){};
  ~BoolectorFunc()
  {
    if (!contains_op)
    {
      boolector_release(btor, node);
    }
  }
  bool is_uf() const override { return !contains_op; };
  bool is_op() const override { return contains_op; };
  Sort get_sort() const override
  {
    if (!contains_op)
    {
      return sort;
    }
    else
    {
      throw IncorrectUsageException("Can't get sort from non-UF function.");
    }
  }
  Op get_op() const override
  {
    if (contains_op)
    {
      return op;
    }
    else
    {
      throw IncorrectUsageException("Can't get op from UF function");
    }
  }
  std::string get_name() const override
  {
    if (!contains_op)
    {
      const char* btor_symbol = boolector_get_symbol(btor, node);
      std::string symbol(btor_symbol);
      return symbol;
    }
    else
    {
      throw IncorrectUsageException("Can't get name from non-UF function.");
    }
  }

 private:
  Op op;
  Btor* btor;
  BoolectorNode* node;
  Sort sort;
  bool contains_op;

  friend class BoolectorSolver;
};

// Boolector PrimOp mappings
typedef BoolectorNode* (*un_fun)(Btor*, BoolectorNode*);
typedef BoolectorNode* (*bin_fun)(Btor*, BoolectorNode*, BoolectorNode*);
typedef BoolectorNode* (*tern_fun)(Btor*,
                                   BoolectorNode*,
                                   BoolectorNode*,
                                   BoolectorNode*);

const std::unordered_map<PrimOp, un_fun> unary_ops({{Not, boolector_not},
                                                    {BVNot, boolector_not},
                                                    {BVNeg, boolector_neg}});

// Indexed Operators are implemented in boolector_solver.h in apply
const std::unordered_map<PrimOp, bin_fun> binary_ops(
    { { And, boolector_and },
      { Or, boolector_or },
      { Xor, boolector_xor },
      { Implies, boolector_implies },
      { Iff, boolector_iff },
      { Equal, boolector_eq },
      { Distinct, boolector_ne },
      { Concat, boolector_concat },
      // Indexed Op: Extract
      { BVAnd, boolector_and },
      { BVOr, boolector_or },
      { BVXor, boolector_xor },
      { BVNand, boolector_nand },
      { BVNor, boolector_nor },
      { BVXnor, boolector_xnor },
      { BVComp, boolector_eq },
      { BVAdd, boolector_add },
      { BVSub, boolector_sub },
      { BVMul, boolector_mul },
      { BVUdiv, boolector_udiv },
      { BVSdiv, boolector_sdiv },
      { BVUrem, boolector_urem },
      { BVSrem, boolector_srem },
      { BVSmod, boolector_smod },
      { BVShl, boolector_sll },
      { BVAshr, boolector_sra },
      { BVLshr, boolector_srl },
      { BVUlt, boolector_ult },
      { BVUle, boolector_ulte },
      { BVUgt, boolector_ugt },
      { BVUge, boolector_ugte },
      { BVSlt, boolector_slt },
      { BVSle, boolector_slte },
      { BVSgt, boolector_sgt },
      { BVSge, boolector_sgte },
      // Indexed Op: Zero_Extend
      // Indexed Op: Sign_Extend
      // Indexed Op: Repeat
      // Indexed Op: Rotate_Left
      // Indexed Op: Rotate_Right
      { Select, boolector_read } });

const std::unordered_map<PrimOp, tern_fun> ternary_ops(
    { { Ite, boolector_cond }, { Store, boolector_write } });
}  // namespace smt

#endif
