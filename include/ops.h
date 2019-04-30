#ifndef SMT_OPS_H
#define SMT_OPS_H

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
   BVEXTRACT,
   SELECT,
   STORE
  }

  union FunctionOrBuiltinOp
  {
    BuiltinOp builtin_op;
    std::shared_ptr<AbsFunction> function;
  }

  struct Op
  {
    bool builtin;
    FunctionOrBuiltinOp op;
  }
}

#endif
