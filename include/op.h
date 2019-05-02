#include "function.h"
#include "prim_ops.h"

#include <memory>
#include <variant>

namespace smt {
class AbsIndexedOp {
public:
  AbsIndexedOp(PrimOp o) : op(o){};
  PrimOp get_prim_op() const { return op; };
protected:
  PrimOp op;
}

using IndexedOp = std::shared_ptr<AbsIndexedOp>;

using Op = std::variant<PrimOp, IndexedOp, Function>;
} // namespace smt

// old attempt
// not advised to use a shared_ptr in a union
// makes sense
// TODO figure out if there's a better way than the struct implementation below
/* union FunctionOrPrimOp */
/* { */
/*   PrimOp builtin_op; */
/*   std::shared_ptr<AbsFunction> function; */
/* }; */

/* // TODO: Implement comparators for comparing Ops and easy comparison to
 * builtin ops / functions */
/* struct Op */
/* { */
/*   bool builtin; */
/*   PrimOp builtin_op; */
/*   // TODO: Are there operators indexed by other types? */
/*   /\* int index1; *\/ */
/*   /\* int index2; *\/ */
/*   std::shared_ptr<AbsFunction> function; */

/* /\* Op(PrimOp bop) *\/ */
/* /\*   : builtin(true), builtin_op(bop), index1(-1), index2(-1),
 * function(nullptr) *\/ */
/* /\*   {}; *\/ */
/* /\* Op(PrimOp bop, int idx1) *\/ */
/* /\*   : builtin(true), builtin_op(bop), index1(idx1), index2(-1),
 * function(nullptr) *\/ */
/* /\*   {}; *\/ */
/* /\* Op(PrimOp bop, int idx1, int idx2) *\/ */
/* /\*   : builtin(true), builtin_op(bop), index1(idx1), index2(idx2),
 * function(nullptr) *\/ */
/* /\*   {}; *\/ */
/* Op(std::shared_ptr<AbsFunction> f) : builtin(false),
 * builtin_op(NUM_OPS_AND_NULL), function(f) {}; */
/* /\* Op(const Op& o) : builtin(o.builtin) *\/ */
/* /\* { *\/ */
/* /\*   if(o.builtin) *\/ */
/* /\*   { *\/ */
/* /\*     builtin_op = o.builtin_op; *\/ */
/* /\*   } *\/ */
/* /\*   else *\/ */
/* /\*   { *\/ */
/* /\*     function = o.function; *\/ */
/* /\*   } *\/ */
/* /\* } *\/ */

/* /\* ~Op() *\/ */
/* /\* { *\/ */
/* /\*   if(builtin) *\/ */
/* /\*     { *\/ */
/* /\*     } *\/ */
/* /\* } *\/ */

/* }; */
