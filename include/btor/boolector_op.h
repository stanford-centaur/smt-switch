#ifndef SMT_BOOLECTOR_OP_H
#define SMT_BOOLECTOR_OP_H

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
    unsigned int get_upper() const { throw IncorrectUsageException("Expecting BoolectorExtractOp."); };
    unsigned int get_lower() const { throw IncorrectUsageException("Expecting BoolectorExtractOp."); };
    unsigned int get_idx() const { throw IncorrectUsageException("Expecting Op with single index"); };

    friend class BoolectorSolver;
  };

  // boolector doesn't have a node type for indexed ops (only functions for performing them)
  // thus we track the information here

  class BoolectorExtractOp : public BoolectorIndexedOp
  {
  public:
    BoolectorExtractOp(PrimOp o, unsigned int u, unsigned int l)
      : BoolectorIndexedOp(o), upper(u), lower(l) {};
    unsigned int get_upper() const { return upper; };
    unsigned int get_lower() const { return lower; };
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
    unsigned int get_idx() const { return idx; };
  protected:
    unsigned int idx;

    friend class BoolectorSolver;
  };

}

#endif
