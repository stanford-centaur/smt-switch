/*********************                                                        */
/*! \file yices2-gtest.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
**
**
**/

#include "gtest/gtest.h"
#include "smt.h"
#include "yices2_factory.h"

using namespace smt;
using namespace std;

namespace {

class Yices2SolverTest : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    s = Yices2SolverFactory::create(true);
    s->set_opt("produce-models", "true");
    bvsort8 = s->make_sort(BV, 8);
    x = s->make_symbol("x", bvsort8);
    y = s->make_symbol("y", bvsort8);
    z = s->make_symbol("z", bvsort8);

    int_sort = s->make_sort(INT);
    a = s->make_symbol("a", int_sort);
    b = s->make_symbol("b", int_sort);
    c = s->make_symbol("c", int_sort);

    bvsort4 = s->make_sort(BV, 4);
    arr_sort = s->make_sort(ARRAY, int_sort, bvsort8);

    arr = s->make_symbol("arr", arr_sort);

    funsort = s->make_sort(FUNCTION, SortVec{ bvsort8, bvsort4 });
    f = s->make_symbol("f", funsort);
  }
  SmtSolver s;
  Sort bvsort8, bvsort4, int_sort, arr_sort, funsort;
  Term x, y, z, a, b, c, arr, f;
};

TEST_F(Yices2SolverTest, TermEquality)
{
  Term q = x;
  EXPECT_TRUE(q == x);
}

TEST_F(Yices2SolverTest, TestEqualOp)
{
  Term t = s->make_term(Equal, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
  EXPECT_TRUE(t->get_op() == Equal);
}

TEST_F(Yices2SolverTest, TestAndOp)
{
  Term t =
      s->make_term(And, s->make_term(Equal, x, y), s->make_term(Equal, y, z));
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
  // Yices has no And term type.
}

TEST_F(Yices2SolverTest, TestOrOp)
{
  Term t =
      s->make_term(Or, s->make_term(Equal, x, y), s->make_term(Equal, y, z));
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
  EXPECT_TRUE(t->get_op() == Or);
}

TEST_F(Yices2SolverTest, TestXorOp)
{
  Term t =
      s->make_term(Xor, s->make_term(Equal, x, y), s->make_term(Equal, y, z));
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestNotOp)
{
  Term t = s->make_term(Not, s->make_term(Equal, x, y));
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
  EXPECT_TRUE(t->get_op() == Not);
}
TEST_F(Yices2SolverTest, TestImpliesOp)
{
  Term t = s->make_term(
      Implies, s->make_term(Equal, x, y), s->make_term(Equal, z, y));
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
  // Yices has no Implies term type.
}

TEST_F(Yices2SolverTest, TestIffOp)
{
  Term t =
      s->make_term(Iff, s->make_term(Equal, x, y), s->make_term(Equal, x, z));
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
  // Yices has no Iff term type.
}

TEST_F(Yices2SolverTest, TestIteOp)
{
  Term t = s->make_term(Ite,
                        s->make_term(Equal, x, y),
                        s->make_term(Equal, x, z),
                        s->make_term(Equal, y, z));
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestDistinctOp)
{
  Term t = s->make_term(Distinct, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
  // Yices keeps evaluating this as T/F or equality.
  // EXPECT_TRUE(t->get_op() == Distinct);
}
TEST_F(Yices2SolverTest, TestSelectOp)
{
  Term t = s->make_term(Select, arr, a);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
  EXPECT_TRUE(t->get_op() == Select);
}

TEST_F(Yices2SolverTest, TestApplyOp)
{
  Term t = s->make_term(Apply, f, x);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
  EXPECT_TRUE(t->get_op() == Apply);
}

TEST_F(Yices2SolverTest, TestPlusOp)
{
  Term t = s->make_term(Plus, a, b);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestMinusOp)
{
  Term t = s->make_term(Minus, a, b);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestNegateOp)
{
  Term t = s->make_term(Negate, a);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestMultOp)
{
  Term t = s->make_term(Mult, a, b);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestDivOp)
{
  Term t = s->make_term(Div, a, b);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestLtOp)
{
  Term t = s->make_term(Lt, a, b);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestLeOp)
{
  Term t = s->make_term(Le, a, b);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestGtOp)
{
  Term t = s->make_term(Gt, a, b);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestGeOp)
{
  Term t = s->make_term(Ge, a, b);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestModOp)
{
  Term t = s->make_term(Mod, a, b);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestAbsOp)
{
  Term t = s->make_term(Abs, a);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestPowOp)
{
  Term t = s->make_term(Pow, a, s->make_term("2", int_sort));
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestBVNegOp)
{
  Term t = s->make_term(BVNeg, x);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestBVAddOp)
{
  Term t = s->make_term(BVAdd, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVSubOp)
{
  Term t = s->make_term(BVSub, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVMulOp)
{
  Term t = s->make_term(BVMul, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVUdivOp)
{
  Term t = s->make_term(BVUdiv, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVSdivOp)
{
  Term t = s->make_term(BVSdiv, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVUremOp)
{
  Term t = s->make_term(BVUrem, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVSremOp)
{
  Term t = s->make_term(BVSrem, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVSmodOp)
{
  Term t = s->make_term(BVSmod, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVShlOp)
{
  Term t = s->make_term(BVShl, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVAshrOp)
{
  Term t = s->make_term(BVAshr, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVLshrOp)
{
  Term t = s->make_term(BVLshr, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVUltOp)
{
  Term t = s->make_term(BVUlt, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVUleOp)
{
  Term t = s->make_term(BVUle, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVUgtOp)
{
  Term t = s->make_term(BVUgt, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVUgeOp)
{
  Term t = s->make_term(BVUge, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVSltOp)
{
  Term t = s->make_term(BVSlt, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVSleOp)
{
  Term t = s->make_term(BVSle, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestVSgtOp)
{
  Term t = s->make_term(BVSgt, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVSgeOp)
{
  Term t = s->make_term(BVSge, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

// TODO
TEST_F(Yices2SolverTest, TestBVNotOp)
{
  Term t = s->make_term(BVNot, x);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVAndOp)
{
  Term t = s->make_term(BVAnd, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}

TEST_F(Yices2SolverTest, TestBVOrOp)
{
  Term t = s->make_term(BVOr, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVXorOp)
{
  Term t = s->make_term(BVXor, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVNandOp)
{
  Term t = s->make_term(BVNand, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVNorOp)
{
  Term t = s->make_term(BVNor, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVXnorOp)
{
  Term t = s->make_term(BVXnor, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
TEST_F(Yices2SolverTest, TestBVCompOp)
{
  Term t = s->make_term(BVComp, x, y);
  EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
}
// end todo

// TEST_F(Yices2SolverTest, TestToRealOp)
// {
//   Term t = s->make_term(To_Real, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }
// TEST_F(Yices2SolverTest, TestToIntOp)
// {
//   Term t = s->make_term(To_Int, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }
// TEST_F(Yices2SolverTest, TestIsIntOp)
// {
//   Term t = s->make_term(Is_Int, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }
// TEST_F(Yices2SolverTest, TestConcatOp)
// {
//   Term t = s->make_term(Concat, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }
// TEST_F(Yices2SolverTest, TestExtractOp)
// {
//   Term t = s->make_term(Extract, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }
// TEST_F(Yices2SolverTest, TestZeroExtendOp)
// {
//   Term t = s->make_term(Zero_Extend, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }
// TEST_F(Yices2SolverTest, TestSignExtendOp)
// {
//   Term t = s->make_term(Sign_Extend, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }
// TEST_F(Yices2SolverTest, TestRepeatOp)
// {
//   Term t = s->make_term(Repeat, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }
// TEST_F(Yices2SolverTest, TestRotateLeftOp)
// {
//   Term t = s->make_term(Rotate_Left, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }
// TEST_F(Yices2SolverTest, TestRotateRightOp)
// {
//   Term t = s->make_term(Rotate_Right, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }
// TEST_F(Yices2SolverTest, TestBVToNatOp)
// {
//   Term t = s->make_term(BV_To_Nat, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }
// TEST_F(Yices2SolverTest, TestIntToBVOp)
// {
//   Term t = s->make_term(Int_To_BV, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }

// TEST_F(Yices2SolverTest, TestStoreOp)
// {
//   Term t = s->make_term(Store, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }
// TEST_F(Yices2SolverTest, TestConstArrayOp)
// {
//   Term t = s->make_term(Const_Array, t1, t2);
//   EXPECT_FALSE(t->get_op() == NUM_OPS_AND_NULL);
// }

}  // namespace
