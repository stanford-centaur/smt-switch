#include <gtest/gtest.h>

#include "ops.h"

using namespace smt;
using namespace std;

TEST(UnitFun, OpEquality)
{
  Op f1(And);
  EXPECT_EQ(f1.num_idx, 0);
  EXPECT_EQ(f1.prim_op, And);
  Op f2(And);
  Op f3(Or);
  EXPECT_EQ(f1, f2);
  EXPECT_NE(f1, f3);

  Op zext(Zero_Extend, 4);
  Op zext2(Zero_Extend, 4);
  Op zext3(Zero_Extend, 5);
  EXPECT_EQ(zext, zext2);
  EXPECT_NE(zext, zext3);

  Op ext(Extract, 3, 0);
  Op ext2(Extract, 3, 0);
  Op ext3(Extract, 3, 1);
  EXPECT_EQ(ext, ext2);
  EXPECT_NE(ext, ext3);
}
