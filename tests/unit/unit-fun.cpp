/*!
 * \file unit-fun.cpp
 * \brief Tests that ops compare equal by their kind and indices
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <string>

#include "smt-switch/ops.h"

namespace smt::tests {

namespace {

TEST(UnitFun, OpEquality)
{
  Op f1(Op::And);
  EXPECT_TRUE(f1.indices.empty());
  EXPECT_EQ(f1.kind(), Op::And);
  Op f2(Op::And);
  Op f3(Op::Or);
  EXPECT_EQ(f1, f2);
  EXPECT_NE(f1, f3);

  Op zext(Op::Zero_Extend, 4);
  Op zext2(Op::Zero_Extend, 4);
  Op zext3(Op::Zero_Extend, 5);
  EXPECT_EQ(zext, zext2);
  EXPECT_NE(zext, zext3);

  Op ext(Op::Extract, 3, 0);
  Op ext2(Op::Extract, 3, 0);
  Op ext3(Op::Extract, 3, 1);
  EXPECT_EQ(ext, ext2);
  EXPECT_NE(ext, ext3);
}

}  // namespace

}  // namespace smt::tests
