#include "assert.h"

#include "ops.h"

using namespace smt;
int main()
{
  Op op1(AND);
  assert(op1.builtin);
  assert(op1.builtin_op == AND);
  assert(op1.function == nullptr);

  Op op2(std::shared_ptr<AbsFunction>(nullptr));
  assert(!op2.builtin);
  assert(op2.builtin_op == NUM_OPS_AND_NULL); // this is an invalid op
  // TODO: change this to something interesting
  assert(op2.function == nullptr);
}
