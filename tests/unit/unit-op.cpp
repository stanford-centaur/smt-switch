/*!
 * \file unit-op.cpp
 * \brief Unit tests for ops
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
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
#include "smt-switch/solver_utils.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt::tests {

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitOpKindTests);
class UnitOpKindTests : public testing::Test,
                        // passing the operator kind as a size_t
                        public testing::WithParamInterface<size_t>
{
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTests);
class UnitTests : public testing::Test,
                  public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    boolsort = s->make_sort(SortKind::BOOL);
    bvsort = s->make_sort(SortKind::BV, 4);
    funsort = s->make_sort(SortKind::FUNCTION, SortVec{ bvsort, bvsort });
  }
  SmtSolver s;
  Sort boolsort, bvsort, funsort;
};

TEST_P(UnitOpKindTests, GetArity)
{
  Op::Kind kind = static_cast<Op::Kind>(GetParam());
  ASSERT_NO_THROW(get_arity(kind));
}

TEST_P(UnitOpKindTests, NaryArity)
{
  Op::Kind kind = static_cast<Op::Kind>(GetParam());
  int attributes = is_left_assoc(kind) + is_right_assoc(kind)
                   + is_chainable(kind) + is_pairwise(kind);
  // SMT-LIB gives an operator at most one of these
  EXPECT_LE(attributes, 1);
  if (attributes)
  {
    // TermTranslator checks the number of arguments against get_arity
    const std::pair<std::size_t, std::size_t> from_two(2, INT_MAX);
    EXPECT_EQ(get_arity(kind), from_two);
  }
}

TEST_P(UnitOpKindTests, ToString)
{
  Op::Kind kind = static_cast<Op::Kind>(GetParam());
  ASSERT_NO_THROW(smt::to_string(kind));
}

TEST_P(UnitOpKindTests, IndicesFitOp)
{
  Op::Kind kind = static_cast<Op::Kind>(GetParam());
  ASSERT_NO_THROW(get_theory(kind));
  // an Op holds at most two indices
  EXPECT_LE(get_num_indices(kind), 2);
}

TEST_P(UnitTests, FunOp)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Op::Apply, f, x);

  ASSERT_EQ(fx->get_op(), Op::Apply);
}

TEST_P(UnitTests, IndexedOps1)
{
  Term x = s->make_symbol("x", bvsort);
  Op ext = Op(Op::Extract, 2, 0);
  Term ext_x = s->make_term(ext, x);
  ASSERT_EQ(ext_x->get_op(), ext);

  Op rep = Op(Op::Repeat, 2);
  Term rep_x = s->make_term(rep, x);
  // some solvers rewrite -- might be concats
  // but we can check the sort
  ASSERT_EQ(rep_x->get_sort()->get_width(), 8);

  Op se = Op(Op::Sign_Extend, 4);
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
  EXPECT_TRUE(Op(Op::BVAdd).indices.empty());

  const Op extend(Op::Zero_Extend, 5);
  EXPECT_EQ(extend.indices.size(), 1);
  EXPECT_EQ(extend.indices[0], 5);
  EXPECT_THROW(extend.indices[1], IncorrectUsageException);

  const Op extract(Op::Extract, 2, 0);
  EXPECT_EQ(extract.indices.size(), 2);
  EXPECT_EQ(extract.indices[0], 2);
  EXPECT_EQ(extract.indices[1], 0);
}

TEST(UnitOpIndexTests, IndexCountMustMatchTheOperator)
{
  EXPECT_THROW(Op{ Op::Extract }, IncorrectUsageException);
  EXPECT_THROW((Op{ Op::Extract, 3 }), IncorrectUsageException);
  EXPECT_THROW((Op{ Op::Repeat, 2, 0 }), IncorrectUsageException);
  EXPECT_THROW((Op{ Op::BVAdd, 1 }), IncorrectUsageException);
}

TEST(UnitOpIndexTests, NarrowIndexRejectsTooLarge)
{
  constexpr std::uint64_t max32 = std::numeric_limits<std::uint32_t>::max();
  Op op = Op(Op::Extract, 2, 0);

  ASSERT_EQ(backend::narrow_index(op, 0), 0);
  ASSERT_EQ(backend::narrow_index(op, max32), max32);
  ASSERT_THROW(backend::narrow_index(op, max32 + 1), IncorrectUsageException);
}

TEST(Narrow, UnsignedToNarrowerUnsigned)
{
  constexpr std::uint64_t max = std::numeric_limits<std::uint32_t>::max();
  EXPECT_EQ(backend::narrow<std::uint32_t>(max, "a value"), max);
  EXPECT_THROW(backend::narrow<std::uint32_t>(max + 1, "a value"),
               IncorrectUsageException);
}

TEST(Narrow, UnsignedToSigned)
{
  constexpr std::uint64_t max = std::numeric_limits<std::int32_t>::max();
  EXPECT_EQ(backend::narrow<std::int32_t>(max, "a value"), max);
  EXPECT_THROW(backend::narrow<std::int32_t>(max + 1, "a value"),
               IncorrectUsageException);
}

TEST(Narrow, SignedToNarrowerSigned)
{
  constexpr std::int64_t min = std::numeric_limits<std::int32_t>::min();
  constexpr std::int64_t max = std::numeric_limits<std::int32_t>::max();
  EXPECT_EQ(backend::narrow<std::int32_t>(min, "a value"), min);
  EXPECT_EQ(backend::narrow<std::int32_t>(max, "a value"), max);
  EXPECT_THROW(backend::narrow<std::int32_t>(min - 1, "a value"),
               IncorrectUsageException);
  EXPECT_THROW(backend::narrow<std::int32_t>(max + 1, "a value"),
               IncorrectUsageException);
}

TEST(Narrow, SignedToUnsigned)
{
  constexpr std::int64_t max = std::numeric_limits<std::uint32_t>::max();
  EXPECT_EQ(backend::narrow<std::uint32_t>(std::int64_t{ 0 }, "a value"), 0u);
  EXPECT_EQ(backend::narrow<std::uint32_t>(max, "a value"), max);
  EXPECT_THROW(backend::narrow<std::uint32_t>(std::int64_t{ -1 }, "a value"),
               IncorrectUsageException);
  EXPECT_THROW(backend::narrow<std::uint32_t>(max + 1, "a value"),
               IncorrectUsageException);
}

TEST(Narrow, WiderTypeKeepsEveryValue)
{
  constexpr std::uint32_t umax = std::numeric_limits<std::uint32_t>::max();
  constexpr std::int32_t smin = std::numeric_limits<std::int32_t>::min();
  EXPECT_EQ(backend::narrow<std::uint64_t>(umax, "a value"), umax);
  EXPECT_EQ(backend::narrow<std::int64_t>(smin, "a value"), smin);
  EXPECT_EQ(backend::narrow<std::int64_t>(umax, "a value"), umax);
}

TEST(UnitOpKindInfoTests, NullHasNoArity)
{
  EXPECT_THROW(get_arity(Op::NONE), IncorrectUsageException);
}

TEST(UnitOpKindInfoTests, NumIndices)
{
  EXPECT_EQ(get_num_indices(Op::Extract), 2);
  EXPECT_EQ(get_num_indices(Op::Zero_Extend), 1);
  EXPECT_EQ(get_num_indices(Op::Int_To_BV), 1);
  EXPECT_EQ(get_num_indices(Op::Divisible), 1);
  EXPECT_EQ(get_num_indices(Op::BVAdd), 0);
  EXPECT_THROW(get_num_indices(Op::NONE), IncorrectUsageException);
}

TEST(UnitOpKindInfoTests, IsApply)
{
  EXPECT_TRUE(is_apply(Op::Apply));
  EXPECT_TRUE(is_apply(Op::Apply_Constructor));
  EXPECT_TRUE(is_apply(Op::Apply_Selector));
  EXPECT_TRUE(is_apply(Op::Apply_Tester));
  EXPECT_FALSE(is_apply(Op::BVAdd));
  EXPECT_FALSE(is_apply(Op::Select));
  EXPECT_FALSE(is_apply(Op::NONE));
}

TEST(UnitOpKindInfoTests, Theory)
{
  EXPECT_EQ(get_theory(Op::And), Theory::CORE);
  EXPECT_EQ(get_theory(Op::Plus), Theory::ARITH);
  EXPECT_EQ(get_theory(Op::IntDiv), Theory::INTS);
  EXPECT_EQ(get_theory(Op::Divisible), Theory::INTS);
  EXPECT_EQ(get_theory(Op::Div), Theory::REALS);
  EXPECT_EQ(get_theory(Op::To_Real), Theory::REALS_INTS);
  EXPECT_EQ(get_theory(Op::UBV_To_Int), Theory::BITVECTORS);
  EXPECT_EQ(get_theory(Op::StrLt), Theory::STRINGS);
  EXPECT_THROW(get_theory(Op::NONE), IncorrectUsageException);
}

TEST_P(UnitTests, RotateOps)
{
  Term x = s->make_symbol("x", bvsort);
  Term rotate_left = s->make_term(Op(Op::Rotate_Left, 2), x);
  Term rotate_right = s->make_term(Op(Op::Rotate_Right, 2), rotate_left);
  s->assert_formula(s->make_term(Op::Distinct, x, rotate_right));
  Result r = s->check_sat();
  ASSERT_TRUE(r.is_unsat());
}

TEST_P(UnitTests, BoolFun)
{
  Term b = s->make_symbol("b", boolsort);
  Sort boolfunsort =
      s->make_sort(SortKind::FUNCTION, SortVec{ boolsort, boolsort });
  Term f = s->make_symbol("f", boolfunsort);
  Term fb = s->make_term(Op::Apply, f, b);
}

TEST_P(UnitTests, MultiArgFun)
{
  SortVec argsorts(7, bvsort);
  // return sort
  argsorts.push_back(boolsort);
  Sort multiargsort = s->make_sort(SortKind::FUNCTION, argsorts);
  Term f = s->make_symbol("f", multiargsort);

  TermVec args1{ f };
  TermVec args2{ f };
  for (size_t i = 0; i < 7; i++)
  {
    args1.push_back(s->make_symbol("x" + std::to_string(i), bvsort));
    args2.push_back(s->make_symbol("y" + std::to_string(i), bvsort));
  }

  Term res = s->make_term(Op::Apply, args1);
  ASSERT_EQ(res, s->make_term(Op::Apply, args1));

  Term res2 = s->make_term(Op::Apply, args2);
  ASSERT_NE(res, res2);
  ASSERT_EQ(res2, s->make_term(Op::Apply, args2));
}

INSTANTIATE_TEST_SUITE_P(ParameterizedOpKind,
                         UnitOpKindTests,
                         testing::Range(size_t{ 1 }, Op::num_kinds));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverUnit,
    UnitTests,
    testing::ValuesIn(filter_solver_configurations_with_generic(
        { SolverAttribute::TERMITER })));

}  // namespace

}  // namespace smt::tests
