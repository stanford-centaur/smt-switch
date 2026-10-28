/*!
 * \file test-op-round-trip.cpp
 * \brief Checks that a term can be rebuilt from its op and children.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Walkers and the term translator take a term apart with get_op() and its
 * children, and build it again with make_term. Each check builds one
 * operator's term and expects that to give back the same term.
 */

#include <gtest/gtest.h>

#include "available_solvers.h"
#include "ops.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"

using namespace smt;
using namespace smt_tests;

namespace {

class OpRoundTripTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    boolsort = s->make_sort(BOOL);
    p = s->make_symbol("p", boolsort);
    q = s->make_symbol("q", boolsort);
    r = s->make_symbol("r", boolsort);
  }

  /** Expects t to be rebuilt from its op and children, none of them t. */
  void expect_round_trip(const Term & t)
  {
    Op op = t->get_op();
    ASSERT_FALSE(op.is_null()) << t;
    TermVec children(t->begin(), t->end());
    ASSERT_FALSE(children.empty()) << t;
    for (const Term & child : children)
    {
      EXPECT_NE(child, t) << t << " is its own child";
    }
    Term rebuilt = s->make_term(op, children);
    EXPECT_EQ(rebuilt, t) << t << " read back as " << op << " over "
                          << children.size() << " children, giving " << rebuilt;
  }

  SmtSolver s;
  Sort boolsort;
  Term p, q, r;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(BoolRoundTripTests);
class BoolRoundTripTests : public OpRoundTripTests
{
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(BVRoundTripTests);
class BVRoundTripTests : public OpRoundTripTests
{
 protected:
  void SetUp() override
  {
    OpRoundTripTests::SetUp();
    bvsort = s->make_sort(BV, 4);
    x = s->make_symbol("x", bvsort);
    y = s->make_symbol("y", bvsort);
  }
  Sort bvsort;
  Term x, y;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IntRoundTripTests);
class IntRoundTripTests : public OpRoundTripTests
{
 protected:
  void SetUp() override
  {
    OpRoundTripTests::SetUp();
    intsort = s->make_sort(INT);
    a = s->make_symbol("a", intsort);
    b = s->make_symbol("b", intsort);
  }
  Sort intsort;
  Term a, b;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(RealRoundTripTests);
class RealRoundTripTests : public OpRoundTripTests
{
 protected:
  void SetUp() override
  {
    OpRoundTripTests::SetUp();
    intsort = s->make_sort(INT);
    a = s->make_symbol("a", intsort);
    Sort realsort = s->make_sort(REAL);
    u = s->make_symbol("u", realsort);
    v = s->make_symbol("v", realsort);
  }
  Sort intsort;
  Term a, u, v;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IntBVRoundTripTests);
class IntBVRoundTripTests : public OpRoundTripTests
{
 protected:
  void SetUp() override
  {
    OpRoundTripTests::SetUp();
    if (GetParam().solver_enum == YICES2)
    {
      GTEST_SKIP() << "Yices2 has no conversion between Int and bit-vectors, "
                      "so it can only apply one to a value";
    }
    intsort = s->make_sort(INT);
    a = s->make_symbol("a", intsort);
    bvsort = s->make_sort(BV, 4);
    x = s->make_symbol("x", bvsort);
  }
  Sort intsort, bvsort;
  Term a, x;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ArrayRoundTripTests);
class ArrayRoundTripTests : public OpRoundTripTests
{
 protected:
  void SetUp() override
  {
    OpRoundTripTests::SetUp();
    bvsort = s->make_sort(BV, 4);
    x = s->make_symbol("x", bvsort);
    y = s->make_symbol("y", bvsort);
    arr = s->make_symbol("arr", s->make_sort(ARRAY, bvsort, bvsort));
  }
  Sort bvsort;
  Term x, y, arr;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(FunRoundTripTests);
class FunRoundTripTests : public OpRoundTripTests
{
 protected:
  void SetUp() override
  {
    OpRoundTripTests::SetUp();
    bvsort = s->make_sort(BV, 4);
    x = s->make_symbol("x", bvsort);
    y = s->make_symbol("y", bvsort);
    f = s->make_symbol("f", s->make_sort(FUNCTION, SortVec{ bvsort, bvsort }));
    g = s->make_symbol(
        "g", s->make_sort(FUNCTION, SortVec{ bvsort, bvsort, boolsort }));
  }
  Sort bvsort;
  Term x, y, f, g;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(QuantifierRoundTripTests);
class QuantifierRoundTripTests : public OpRoundTripTests
{
 protected:
  void SetUp() override
  {
    OpRoundTripTests::SetUp();
    if (GetParam().solver_enum == BTOR)
    {
      GTEST_SKIP() << "Boolector binds a param in one quantifier only";
    }
    if (GetParam().solver_enum == Z3 && !GetParam().is_logging_solver)
    {
      GTEST_SKIP() << "Z3 cannot iterate over a quantifier's children";
    }
    bvsort = s->make_sort(BV, 4);
    x = s->make_symbol("x", bvsort);
    i = s->make_param("i", bvsort);
  }
  Sort bvsort;
  Term x, i;
};

TEST_P(BoolRoundTripTests, Equal)
{
  expect_round_trip(s->make_term(Equal, p, q));
}

TEST_P(BoolRoundTripTests, And) { expect_round_trip(s->make_term(And, p, q)); }

TEST_P(BoolRoundTripTests, Or) { expect_round_trip(s->make_term(Or, p, q)); }

TEST_P(BoolRoundTripTests, Xor) { expect_round_trip(s->make_term(Xor, p, q)); }

TEST_P(BoolRoundTripTests, Not) { expect_round_trip(s->make_term(Not, p)); }

TEST_P(BoolRoundTripTests, Implies)
{
  expect_round_trip(s->make_term(Implies, p, q));
}

TEST_P(BoolRoundTripTests, Ite)
{
  expect_round_trip(s->make_term(Ite, p, q, r));
}

TEST_P(BoolRoundTripTests, Distinct)
{
  expect_round_trip(s->make_term(Distinct, p, q));
}

TEST_P(BVRoundTripTests, BVNot) { expect_round_trip(s->make_term(BVNot, x)); }

TEST_P(BVRoundTripTests, BVNeg) { expect_round_trip(s->make_term(BVNeg, x)); }

TEST_P(BVRoundTripTests, BVAnd)
{
  expect_round_trip(s->make_term(BVAnd, x, y));
}

TEST_P(BVRoundTripTests, BVOr) { expect_round_trip(s->make_term(BVOr, x, y)); }

TEST_P(BVRoundTripTests, BVXor)
{
  expect_round_trip(s->make_term(BVXor, x, y));
}

TEST_P(BVRoundTripTests, BVNand)
{
  expect_round_trip(s->make_term(BVNand, x, y));
}

TEST_P(BVRoundTripTests, BVNor)
{
  expect_round_trip(s->make_term(BVNor, x, y));
}

TEST_P(BVRoundTripTests, BVXnor)
{
  expect_round_trip(s->make_term(BVXnor, x, y));
}

TEST_P(BVRoundTripTests, BVComp)
{
  expect_round_trip(s->make_term(BVComp, x, y));
}

TEST_P(BVRoundTripTests, BVAdd)
{
  expect_round_trip(s->make_term(BVAdd, x, y));
}

TEST_P(BVRoundTripTests, BVSub)
{
  expect_round_trip(s->make_term(BVSub, x, y));
}

TEST_P(BVRoundTripTests, BVMul)
{
  expect_round_trip(s->make_term(BVMul, x, y));
}

TEST_P(BVRoundTripTests, BVUdiv)
{
  expect_round_trip(s->make_term(BVUdiv, x, y));
}

TEST_P(BVRoundTripTests, BVSdiv)
{
  expect_round_trip(s->make_term(BVSdiv, x, y));
}

TEST_P(BVRoundTripTests, BVUrem)
{
  expect_round_trip(s->make_term(BVUrem, x, y));
}

TEST_P(BVRoundTripTests, BVSrem)
{
  expect_round_trip(s->make_term(BVSrem, x, y));
}

TEST_P(BVRoundTripTests, BVSmod)
{
  expect_round_trip(s->make_term(BVSmod, x, y));
}

TEST_P(BVRoundTripTests, BVShl)
{
  expect_round_trip(s->make_term(BVShl, x, y));
}

TEST_P(BVRoundTripTests, BVAshr)
{
  expect_round_trip(s->make_term(BVAshr, x, y));
}

TEST_P(BVRoundTripTests, BVLshr)
{
  expect_round_trip(s->make_term(BVLshr, x, y));
}

TEST_P(BVRoundTripTests, BVUlt)
{
  expect_round_trip(s->make_term(BVUlt, x, y));
}

TEST_P(BVRoundTripTests, BVUle)
{
  expect_round_trip(s->make_term(BVUle, x, y));
}

TEST_P(BVRoundTripTests, BVUgt)
{
  expect_round_trip(s->make_term(BVUgt, x, y));
}

TEST_P(BVRoundTripTests, BVUge)
{
  expect_round_trip(s->make_term(BVUge, x, y));
}

TEST_P(BVRoundTripTests, BVSlt)
{
  expect_round_trip(s->make_term(BVSlt, x, y));
}

TEST_P(BVRoundTripTests, BVSle)
{
  expect_round_trip(s->make_term(BVSle, x, y));
}

TEST_P(BVRoundTripTests, BVSgt)
{
  expect_round_trip(s->make_term(BVSgt, x, y));
}

TEST_P(BVRoundTripTests, BVSge)
{
  expect_round_trip(s->make_term(BVSge, x, y));
}

TEST_P(BVRoundTripTests, Concat)
{
  expect_round_trip(s->make_term(Concat, x, y));
}

TEST_P(BVRoundTripTests, Extract)
{
  expect_round_trip(s->make_term(Op(Extract, 2, 1), x));
}

TEST_P(BVRoundTripTests, ZeroExtend)
{
  expect_round_trip(s->make_term(Op(Zero_Extend, 2), x));
}

TEST_P(BVRoundTripTests, SignExtend)
{
  expect_round_trip(s->make_term(Op(Sign_Extend, 2), x));
}

TEST_P(BVRoundTripTests, Repeat)
{
  expect_round_trip(s->make_term(Op(Repeat, 2), x));
}

TEST_P(BVRoundTripTests, RotateLeft)
{
  expect_round_trip(s->make_term(Op(Rotate_Left, 2), x));
}

TEST_P(BVRoundTripTests, RotateRight)
{
  expect_round_trip(s->make_term(Op(Rotate_Right, 2), x));
}

TEST_P(BVRoundTripTests, SumOfProduct)
{
  expect_round_trip(s->make_term(BVAdd, x, s->make_term(BVMul, y, x)));
}

TEST_P(IntRoundTripTests, Plus) { expect_round_trip(s->make_term(Plus, a, b)); }

TEST_P(IntRoundTripTests, Minus)
{
  expect_round_trip(s->make_term(Minus, a, b));
}

TEST_P(IntRoundTripTests, Negate)
{
  expect_round_trip(s->make_term(Negate, a));
}

TEST_P(IntRoundTripTests, Mult) { expect_round_trip(s->make_term(Mult, a, b)); }

TEST_P(IntRoundTripTests, IntDiv)
{
  expect_round_trip(s->make_term(IntDiv, a, b));
}

TEST_P(IntRoundTripTests, Mod) { expect_round_trip(s->make_term(Mod, a, b)); }

TEST_P(IntRoundTripTests, Abs) { expect_round_trip(s->make_term(Abs, a)); }

TEST_P(IntRoundTripTests, Pow)
{
  expect_round_trip(s->make_term(Pow, a, s->make_term(4, intsort)));
}

TEST_P(IntRoundTripTests, Lt) { expect_round_trip(s->make_term(Lt, a, b)); }

TEST_P(IntRoundTripTests, Le) { expect_round_trip(s->make_term(Le, a, b)); }

TEST_P(IntRoundTripTests, Gt) { expect_round_trip(s->make_term(Gt, a, b)); }

TEST_P(IntRoundTripTests, Ge) { expect_round_trip(s->make_term(Ge, a, b)); }

TEST_P(IntRoundTripTests, ScaledSum)
{
  expect_round_trip(
      s->make_term(Plus, s->make_term(Mult, s->make_term(2, intsort), a), b));
}

TEST_P(IntRoundTripTests, ScaledTerm)
{
  expect_round_trip(s->make_term(Mult, s->make_term(-1, intsort), b));
}

TEST_P(IntRoundTripTests, ConstantSummand)
{
  expect_round_trip(s->make_term(Plus, a, s->make_term(2, intsort)));
}

TEST_P(RealRoundTripTests, Div) { expect_round_trip(s->make_term(Div, u, v)); }

TEST_P(RealRoundTripTests, ToReal)
{
  Term t = s->make_term(To_Real, a);
  if (t == a)
  {
    GTEST_SKIP() << "the solver treats Int as a subtype of Real, so " << t
                 << " is its own argument";
  }
  expect_round_trip(t);
}

TEST_P(RealRoundTripTests, ToInt)
{
  expect_round_trip(s->make_term(To_Int, u));
}

TEST_P(RealRoundTripTests, IsInt)
{
  expect_round_trip(s->make_term(Is_Int, u));
}

TEST_P(IntBVRoundTripTests, UBVToInt)
{
  expect_round_trip(s->make_term(UBV_To_Int, x));
}

TEST_P(IntBVRoundTripTests, SBVToInt)
{
  expect_round_trip(s->make_term(SBV_To_Int, x));
}

TEST_P(IntBVRoundTripTests, IntToBV)
{
  expect_round_trip(s->make_term(Op(Int_To_BV, 4), a));
}

TEST_P(ArrayRoundTripTests, Select)
{
  expect_round_trip(s->make_term(Select, arr, x));
}

TEST_P(ArrayRoundTripTests, Store)
{
  expect_round_trip(s->make_term(Store, arr, x, y));
}

TEST_P(FunRoundTripTests, ApplyUnary)
{
  expect_round_trip(s->make_term(Apply, f, x));
}

TEST_P(FunRoundTripTests, ApplyBinary)
{
  expect_round_trip(s->make_term(Apply, g, x, y));
}

TEST_P(QuantifierRoundTripTests, Forall)
{
  expect_round_trip(s->make_term(Forall, i, s->make_term(BVUle, i, x)));
}

TEST_P(QuantifierRoundTripTests, Exists)
{
  expect_round_trip(s->make_term(Exists, i, s->make_term(BVUle, i, x)));
}

INSTANTIATE_TEST_SUITE_P(
    ,
    BoolRoundTripTests,
    testing::ValuesIn(filter_solver_configurations({ TERMITER })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ,
    BVRoundTripTests,
    testing::ValuesIn(filter_solver_configurations({ TERMITER, THEORY_BV })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ,
    IntRoundTripTests,
    testing::ValuesIn(filter_solver_configurations({ TERMITER, THEORY_INT })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(,
                         RealRoundTripTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { TERMITER, THEORY_INT, THEORY_REAL })),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(,
                         IntBVRoundTripTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { TERMITER, THEORY_INT, THEORY_BV })),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ,
    ArrayRoundTripTests,
    testing::ValuesIn(filter_solver_configurations({ TERMITER, THEORY_BV })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ,
    FunRoundTripTests,
    testing::ValuesIn(filter_solver_configurations({ TERMITER, THEORY_BV })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(,
                         QuantifierRoundTripTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { TERMITER, THEORY_BV, QUANTIFIERS })),
                         ConfigName());

}  // namespace
