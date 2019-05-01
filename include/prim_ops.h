#ifndef SMT_OPS_H
#define SMT_OPS_H

#include "function.h"

namespace smt
{
  // TODO add more smt ops
  enum PrimOp
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
   // distinguish between const and variable in the leaves
   // TODO: Decide if it should be Value/Const instead
   CONST,
   VAR,
   /**
      Serves as both the number of ops and a null element for builtin operators.
    */
   NUM_OPS_AND_NULL
  };
}

#endif
