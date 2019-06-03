#include "assert.h"

#include "func.h"

using namespace smt;
using namespace std;

int main()
{
  Op f1(And);
  assert(f1.num_idx == 0);
  assert(f1.prim_op == And);
  Op f2(And);
  Op f3(Or);
  assert(f1 == f2);
  assert(f1 != f3);

  Op zext(Zero_Extend, 4);
  Op zext2(Zero_Extend, 4);
  Op zext3(Zero_Extend, 5);
  assert(zext == zext2);
  assert(zext != zext3);

  Op ext(Extract, 3, 0);
  Op ext2(Extract, 3, 0);
  Op ext3(Extract, 3, 1);
  assert(ext == ext2);
  assert(ext != ext3);
}
