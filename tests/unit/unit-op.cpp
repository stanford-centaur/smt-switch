/*********************                                                        */
/*! \file unit-op.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for ops.
**
**
**/

#include <gtest/gtest.h>

#include <climits>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <memory>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/solver_utils.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitPrimOpTests);
class UnitPrimOpTests : public ::testing::Test,
                        // passing the PrimOp enum as a size_t
                        public ::testing::WithParamInterface<size_t>
{
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTests);
class UnitTests : public ::testing::Test,
                  public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
  }
  SmtSolver s;
  Sort boolsort, bvsort, funsort;
};

TEST_P(UnitPrimOpTests, GetArity)
{
  PrimOp po = static_cast<PrimOp>(GetParam());
  ASSERT_NO_THROW(get_arity(po));
}

TEST_P(UnitPrimOpTests, NaryArity)
{
  PrimOp po = static_cast<PrimOp>(GetParam());
  int attributes = is_left_assoc(po) + is_right_assoc(po) + is_chainable(po)
                   + is_pairwise(po);
  // SMT-LIB gives an operator at most one of these
  EXPECT_LE(attributes, 1);
  if (attributes)
  {
    // TermTranslator checks the number of arguments against get_arity
    const std::pair<std::size_t, std::size_t> from_two(2, INT_MAX);
    EXPECT_EQ(get_arity(po), from_two);
  }
}

TEST_P(UnitPrimOpTests, ToString)
{
  PrimOp po = static_cast<PrimOp>(GetParam());
  ASSERT_NO_THROW(::smt::to_string(po));
}

TEST_P(UnitPrimOpTests, IndicesFitOp)
{
  PrimOp po = static_cast<PrimOp>(GetParam());
  ASSERT_NO_THROW(get_theory(po));
  // an Op holds at most two indices
  EXPECT_LE(get_num_indices(po), 2);
}

TEST_P(UnitTests, FunOp)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  ASSERT_EQ(fx->get_op(), Apply);
}

TEST_P(UnitTests, IndexedOps1)
{
  Term x = s->make_symbol("x", bvsort);
  Op ext = Op(Extract, 2, 0);
  Term ext_x = s->make_term(ext, x);
  ASSERT_EQ(ext_x->get_op(), ext);

  Op rep = Op(Repeat, 2);
  Term rep_x = s->make_term(rep, x);
  // some solvers rewrite -- might be concats
  // but we can check the sort
  ASSERT_EQ(rep_x->get_sort()->get_width(), 8);

  Op se = Op(Sign_Extend, 4);
  Term se_x = s->make_term(se, x);
  ASSERT_EQ(se_x->get_sort()->get_width(), 8);
  Op op = se_x->get_op();
  TermVec children;
  for (auto tt : se_x)
  {
    children.push_back(tt);
  }
  Term se_x_rebuilt = s->make_term(op, children);
  ASSERT_EQ(se_x_rebuilt, se_x);
}

// Not parameterized: neither case involves a solver. The narrowing itself is
// only reached by the backends whose API takes 32-bit indices, so testing it
// through make_term would exercise nothing on mathsat or bitwuzla.
TEST(UnitOpIndexTests, IndicesFollowTheConstructor)
{
  EXPECT_TRUE(Op().indices.empty());
  EXPECT_TRUE(Op(BVAdd).indices.empty());

  const Op extend(Zero_Extend, 5);
  EXPECT_EQ(extend.indices.size(), 1);
  EXPECT_EQ(extend.indices[0], 5);
  EXPECT_THROW(extend.indices[1], IncorrectUsageException);

  const Op extract(Extract, 2, 0);
  EXPECT_EQ(extract.indices.size(), 2);
  EXPECT_EQ(extract.indices[0], 2);
  EXPECT_EQ(extract.indices[1], 0);
}

TEST(UnitOpIndexTests, IndexCountMustMatchTheOperator)
{
  EXPECT_THROW(Op{ Extract }, IncorrectUsageException);
  EXPECT_THROW((Op{ Extract, 3 }), IncorrectUsageException);
  EXPECT_THROW((Op{ Repeat, 2, 0 }), IncorrectUsageException);
  EXPECT_THROW((Op{ BVAdd, 1 }), IncorrectUsageException);
}

TEST(UnitOpIndexTests, NarrowIndexRejectsTooLarge)
{
  constexpr std::uint64_t max32 = std::numeric_limits<std::uint32_t>::max();
  Op op = Op(Extract, 2, 0);

  ASSERT_EQ(narrow_index(op, 0), 0);
  ASSERT_EQ(narrow_index(op, max32), max32);
  ASSERT_THROW(narrow_index(op, max32 + 1), IncorrectUsageException);
}

TEST(Narrow, UnsignedToNarrowerUnsigned)
{
  constexpr std::uint64_t max = std::numeric_limits<std::uint32_t>::max();
  EXPECT_EQ(detail::narrow<std::uint32_t>(max, "a value"), max);
  EXPECT_THROW(detail::narrow<std::uint32_t>(max + 1, "a value"),
               IncorrectUsageException);
}

TEST(Narrow, UnsignedToSigned)
{
  constexpr std::uint64_t max = std::numeric_limits<std::int32_t>::max();
  EXPECT_EQ(detail::narrow<std::int32_t>(max, "a value"), max);
  EXPECT_THROW(detail::narrow<std::int32_t>(max + 1, "a value"),
               IncorrectUsageException);
}

TEST(Narrow, SignedToNarrowerSigned)
{
  constexpr std::int64_t min = std::numeric_limits<std::int32_t>::min();
  constexpr std::int64_t max = std::numeric_limits<std::int32_t>::max();
  EXPECT_EQ(detail::narrow<std::int32_t>(min, "a value"), min);
  EXPECT_EQ(detail::narrow<std::int32_t>(max, "a value"), max);
  EXPECT_THROW(detail::narrow<std::int32_t>(min - 1, "a value"),
               IncorrectUsageException);
  EXPECT_THROW(detail::narrow<std::int32_t>(max + 1, "a value"),
               IncorrectUsageException);
}

TEST(Narrow, SignedToUnsigned)
{
  constexpr std::int64_t max = std::numeric_limits<std::uint32_t>::max();
  EXPECT_EQ(detail::narrow<std::uint32_t>(std::int64_t{ 0 }, "a value"), 0u);
  EXPECT_EQ(detail::narrow<std::uint32_t>(max, "a value"), max);
  EXPECT_THROW(detail::narrow<std::uint32_t>(std::int64_t{ -1 }, "a value"),
               IncorrectUsageException);
  EXPECT_THROW(detail::narrow<std::uint32_t>(max + 1, "a value"),
               IncorrectUsageException);
}

TEST(Narrow, WiderTypeKeepsEveryValue)
{
  constexpr std::uint32_t umax = std::numeric_limits<std::uint32_t>::max();
  constexpr std::int32_t smin = std::numeric_limits<std::int32_t>::min();
  EXPECT_EQ(detail::narrow<std::uint64_t>(umax, "a value"), umax);
  EXPECT_EQ(detail::narrow<std::int64_t>(smin, "a value"), smin);
  EXPECT_EQ(detail::narrow<std::int64_t>(umax, "a value"), umax);
}

TEST(UnitPrimOpInfoTests, NullHasNoArity)
{
  EXPECT_THROW(get_arity(NUM_OPS_AND_NULL), IncorrectUsageException);
}

TEST(UnitPrimOpInfoTests, NumIndices)
{
  EXPECT_EQ(get_num_indices(Extract), 2);
  EXPECT_EQ(get_num_indices(Zero_Extend), 1);
  EXPECT_EQ(get_num_indices(Int_To_BV), 1);
  EXPECT_EQ(get_num_indices(Divisible), 1);
  EXPECT_EQ(get_num_indices(BVAdd), 0);
  EXPECT_THROW(get_num_indices(NUM_OPS_AND_NULL), IncorrectUsageException);
}

TEST(UnitPrimOpInfoTests, IsApply)
{
  EXPECT_TRUE(is_apply(Apply));
  EXPECT_TRUE(is_apply(Apply_Constructor));
  EXPECT_TRUE(is_apply(Apply_Selector));
  EXPECT_TRUE(is_apply(Apply_Tester));
  EXPECT_FALSE(is_apply(BVAdd));
  EXPECT_FALSE(is_apply(Select));
  EXPECT_FALSE(is_apply(NUM_OPS_AND_NULL));
}

TEST(UnitPrimOpInfoTests, Theory)
{
  EXPECT_EQ(get_theory(And), Theory::CORE);
  EXPECT_EQ(get_theory(Plus), Theory::ARITH);
  EXPECT_EQ(get_theory(IntDiv), Theory::INTS);
  EXPECT_EQ(get_theory(Divisible), Theory::INTS);
  EXPECT_EQ(get_theory(Div), Theory::REALS);
  EXPECT_EQ(get_theory(To_Real), Theory::REALS_INTS);
  EXPECT_EQ(get_theory(UBV_To_Int), Theory::BITVECTORS);
  EXPECT_EQ(get_theory(StrLt), Theory::STRINGS);
  EXPECT_THROW(get_theory(NUM_OPS_AND_NULL), IncorrectUsageException);
}

TEST_P(UnitTests, RotateOps)
{
  Term x = s->make_symbol("x", bvsort);
  Term rotate_left = s->make_term(Op(Rotate_Left, 2), x);
  Term rotate_right = s->make_term(Op(Rotate_Right, 2), rotate_left);
  s->assert_formula(s->make_term(Distinct, x, rotate_right));
  Result r = s->check_sat();
  ASSERT_TRUE(r.is_unsat());
}

TEST_P(UnitTests, BoolFun)
{
  Term b = s->make_symbol("b", boolsort);
  Sort boolfunsort = s->make_sort(FUNCTION, SortVec{ boolsort, boolsort });
  Term f = s->make_symbol("f", boolfunsort);
  Term fb = s->make_term(Apply, f, b);
}

TEST_P(UnitTests, MultiArgFun)
{
  SortVec argsorts(7, bvsort);
  // return sort
  argsorts.push_back(boolsort);
  Sort multiargsort = s->make_sort(FUNCTION, argsorts);
  Term f = s->make_symbol("f", multiargsort);

  TermVec args1{ f };
  TermVec args2{ f };
  for (size_t i = 0; i < 7; i++)
  {
    args1.push_back(s->make_symbol("x" + std::to_string(i), bvsort));
    args2.push_back(s->make_symbol("y" + std::to_string(i), bvsort));
  }

  Term res = s->make_term(Apply, args1);
  ASSERT_EQ(res, s->make_term(Apply, args1));

  Term res2 = s->make_term(Apply, args2);
  ASSERT_NE(res, res2);
  ASSERT_EQ(res2, s->make_term(Apply, args2));
}

INSTANTIATE_TEST_SUITE_P(ParameterizedPrimOp,
                         UnitPrimOpTests,
                         testing::Range(size_t{ 0 },
                                        static_cast<size_t>(NUM_OPS_AND_NULL)));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverUnit,
    UnitTests,
    testing::ValuesIn(filter_solver_configurations({ TERMITER })));

}  // namespace
