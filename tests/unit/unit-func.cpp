#include "assert.h"

#include "func.h"

using namespace smt;
using namespace std;

int main() {
  Func f1(AND);
  assert(holds_alternative<PrimOp>(f1));
  assert(get<PrimOp>(f1) == AND);
  Func f2(AND);
  assert(f1 == f2);

  IndexedOp io(nullptr);
  Func indexed_op;
  indexed_op = io;
  assert(holds_alternative<IndexedOp>(indexed_op));
  assert(!holds_alternative<UF>(indexed_op));
  Func indexed_op_copy = indexed_op;
  assert(indexed_op_copy == indexed_op);

  UF fun(nullptr);
  Func uninterpreted_func = fun;
  assert(holds_alternative<UF>(uninterpreted_func));
  assert(!holds_alternative<IndexedOp>(uninterpreted_func));
  assert(get<UF>(uninterpreted_func) == fun);
}
