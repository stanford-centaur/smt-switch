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
   VAR,
   NUM_OPS
  };

  // not advised to use a shared_ptr in a union
  // makes sense
  // TODO figure out if there's a better way than the struct implementation below
  /* union FunctionOrBuiltinOp */
  /* { */
  /*   BuiltinOp builtin_op; */
  /*   std::shared_ptr<AbsFunction> function; */
  /* }; */

  struct Op
  {
    bool builtin;
    BuiltinOp builtin_op;
    std::shared_ptr<AbsFunction> function;

  Op(BuiltinOp bop) : builtin(true), builtin_op(bop), function(nullptr) {};
  Op(std::shared_ptr<AbsFunction> f) : builtin(false), builtin_op(NUM_OPS), function(f) {};
  /* Op(const Op& o) : builtin(o.builtin) */
  /* { */
  /*   if(o.builtin) */
  /*   { */
  /*     builtin_op = o.builtin_op; */
  /*   } */
  /*   else */
  /*   { */
  /*     function = o.function; */
  /*   } */
  /* } */

  /* ~Op() */
  /* { */
  /*   if(builtin) */
  /*     { */
        
  /*     } */
  /* } */

  };
}

#endif
