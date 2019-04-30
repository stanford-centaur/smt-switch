#ifndef SMT_OPS_H
#define SMT_OPS_H

#include "function.h"

namespace smt
{
  // TODO add more smt ops
  enum BuiltinOp
  {
   AND=0,
   OR,
   XOR,
   NOT,
   IMPLIES,
   ITE,
   BVAND,
   BVOR,
   BXOR,
   BVNOT,
   BVNEG,
   BVADD,
   BVSUB,
   BVMUL,
   BVASHR,
   BVLSHR,
   BVSHL,
   BVULT,
   BVULE,
   BVUGT,
   BVUGE,
   BVSLT,
   BVSLE,
   BVSGT,
   BVSGE,
   BVEXTRACT,
   SELECT,
   STORE,
   VAR
  };

  union FunctionOrBuiltinOp
  {
    BuiltinOp builtin_op;
    std::shared_ptr<AbsFunction> function;
  };

  struct Op
  {
    bool builtin;
    FunctionOrBuiltinOp op;
  };
}

#endif
