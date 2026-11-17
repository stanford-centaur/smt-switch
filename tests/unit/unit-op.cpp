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
 protected:
  /** The Op of the kind under test, with as many indices as it takes */
  Op make_op() const
  {
    const Op::Kind kind = static_cast<Op::Kind>(GetParam());
    try
    {
      return Op(kind);
    }
    catch (const IncorrectUsageException &)
    {
    }
    try
    {
      return Op(kind, 1);
    }
    catch (const IncorrectUsageException &)
    {
    }
    return Op(kind, 1, 2);
  }
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

TEST_P(UnitOpKindTests, HasAnArity) { ASSERT_NO_THROW(make_op().arity()); }

TEST_P(UnitOpKindTests, NaryArity)
{
  const Op op = make_op();
  int attributes = op.is_left_assoc() + op.is_right_assoc() + op.is_chainable()
                   + op.is_pairwise();
  // SMT-LIB gives an operator at most one of these
  EXPECT_LE(attributes, 1);
  if (attributes)
  {
    // TermTranslator checks the number of arguments against the arity
    const std::pair<std::size_t, std::size_t> from_two(2, INT_MAX);
    EXPECT_EQ(op.arity(), from_two);
  }
}

TEST_P(UnitOpKindTests, ToString)
{
  Op::Kind kind = static_cast<Op::Kind>(GetParam());
  ASSERT_NO_THROW(smt::to_string(kind));
}

TEST_P(UnitOpKindTests, HasATheory) { ASSERT_NO_THROW(make_op().theory()); }

TEST_P(UnitOpKindTests, TakesZeroOneOrTwoIndices)
{
  const Op::Kind kind = static_cast<Op::Kind>(GetParam());
  int accepted = 0;
  try
  {
    const Op op(kind);
    ++accepted;
  }
  catch (const IncorrectUsageException &)
  {
  }
  try
  {
    const Op op(kind, 1);
    ++accepted;
  }
  catch (const IncorrectUsageException &)
  {
  }
  try
  {
    const Op op(kind, 1, 2);
    ++accepted;
  }
  catch (const IncorrectUsageException &)
  {
  }
  EXPECT_EQ(accepted, 1);
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
  EXPECT_THROW(Op().arity(), IncorrectUsageException);
}

TEST(UnitOpKindInfoTests, IsApply)
{
  EXPECT_TRUE(Op(Op::Apply).is_apply());
  EXPECT_TRUE(Op(Op::Apply_Constructor).is_apply());
  EXPECT_TRUE(Op(Op::Apply_Selector).is_apply());
  EXPECT_TRUE(Op(Op::Apply_Tester).is_apply());
  EXPECT_FALSE(Op(Op::BVAdd).is_apply());
  EXPECT_FALSE(Op(Op::Select).is_apply());
  EXPECT_FALSE(Op().is_apply());
}

TEST(UnitOpKindInfoTests, Theory)
{
  EXPECT_EQ(Op(Op::And).theory(), Theory::CORE);
  EXPECT_EQ(Op(Op::Plus).theory(), Theory::ARITH);
  EXPECT_EQ(Op(Op::IntDiv).theory(), Theory::INTS);
  EXPECT_EQ(Op(Op::Divisible, 2).theory(), Theory::INTS);
  EXPECT_EQ(Op(Op::Div).theory(), Theory::REALS);
  EXPECT_EQ(Op(Op::To_Real).theory(), Theory::REALS_INTS);
  EXPECT_EQ(Op(Op::UBV_To_Int).theory(), Theory::BITVECTORS);
  EXPECT_EQ(Op(Op::StrLt).theory(), Theory::STRINGS);
  EXPECT_THROW(Op().theory(), IncorrectUsageException);
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
