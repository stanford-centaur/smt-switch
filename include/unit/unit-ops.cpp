#include "assert.h"

#include "op.h"

using namespace smt;
using namespace std;

int main() {
  Op op1(AND);
  assert(holds_alternative<PrimOp>(op1));
  assert(get<PrimOp>(op1) == AND);
  Op op2(AND);
  assert(op1 == op2);

  IndexedOp io(nullptr);
  Op indexed_op;
  indexed_op = io;
  assert(holds_alternative<IndexedOp>(indexed_op));
  assert(!holds_alternative<Function>(indexed_op));
  Op indexed_op_copy = indexed_op;
  assert(indexed_op_copy == indexed_op);

  Function fun(nullptr);
  Op fun_op = fun;
  assert(holds_alternative<Function>(fun_op));
  assert(!holds_alternative<IndexedOp>(fun_op));
  assert(get<Function>(fun_op) == fun);
}
