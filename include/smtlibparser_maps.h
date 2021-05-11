#include <string>

#include "ops.h"

namespace smt {

const std::unordered_map<SortKind,
                         std::unordered_map<std::string, PrimOp>> str2primop(
    { { BOOL,
        { { "and", And },
          { "or", Or },
          { "xor", Xor },
          { "not", Not },
          { "=>", Implies },
          { "ite", Ite },
          { "=", Equal },
          { "distinct", Distinct },
          // forall / exists parsed explicitly
          // { "forall", Forall },
          // { "exists", Exists },
         }
      },
      { FUNCTION,
        { { "apply", Apply } }
      },
      { INT,
        { { "+", Plus },
          { "-", Minus },
           // Need to pick which one based on context
           // { "-", Negate },
          { "<", Lt },
          { "<=", Le },
          { ">", Gt },
          { ">=", Ge },
          { "*", Mult },
          { "pow", Pow },
          { "div", IntDiv },
          { "mod", Mod },
          { "abs", Abs },
          { "to_real", To_Real },
          { "int2bv", Int_To_BV }
        }
      },
      { REAL,
        { { "+", Plus },
          { "-", Minus },
          // Need to pick which one based on context
          // { "-", Negate },
          { "<", Lt },
          { "<=", Le },
          { ">", Gt },
          { ">=", Ge },
          { "*", Mult },
          { "pow", Pow },
          { "/", Div },
          { "to_int", To_Int },
          { "is_int", Is_Int },
        }
      },
      { BV,
        { { "concat", Concat },
          { "extract", Extract },
          { "bvnot", BVNot },
          { "bvneg", BVNeg },
          { "bvand", BVAnd },
          { "bvor", BVOr },
          { "bvxor", BVXor },
          { "bvnand", BVNand },
          { "bvnor", BVNor },
          { "bvxnor", BVXnor },
          { "bvcomp", BVComp },
          { "bvadd", BVAdd },
          { "bvsub", BVSub },
          { "bvmul", BVMul },
          { "bvudiv", BVUdiv },
          { "bvsdiv", BVSdiv },
          { "bvurem", BVUrem },
          { "bvsrem", BVSrem },
          { "bvsmod", BVSmod },
          { "bvshl", BVShl },
          { "bvashr", BVAshr },
          { "bvlshr", BVLshr },
          { "bvult", BVUlt },
          { "bvule", BVUle },
          { "bvugt", BVUgt },
          { "bvuge", BVUge },
          { "bvslt", BVSlt },
          { "bvsle", BVSle },
          { "bvsgt", BVSgt },
          { "bvsge", BVSge },
          { "zero_extend", Zero_Extend },
          { "sign_extend", Sign_Extend },
          { "repeat", Repeat },
          { "rotate_left", Rotate_Left },
          { "rotate_right", Rotate_Right },
          { "bv2nat", BV_To_Nat },
        }
      },
      { ARRAY,
        { { "select", Select },
          { "store", Store },
        }
      },
      { DATATYPE,
        { { "apply_selector", Apply_Selector },
          { "apply_tester", Apply_Tester },
          { "apply_constructor", Apply_Constructor }
        }
      }
    });

}  // namespace smt
