#ifndef SMT_OP_H
#define SMT_OP_H

#include "uf.h"
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
};

using IndexedOp = std::shared_ptr<AbsIndexedOp>;

using Op = std::variant<PrimOp, IndexedOp, UF>;
} // namespace smt

#endif
