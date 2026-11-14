/*!
 * \file unit-incremental.cpp
 * \brief Unit tests for incremental solving interface
 * \author Makai Mann
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <cstdint>
#include <limits>
#include <string>
#include <unordered_set>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitIncrementalTests);
class UnitIncrementalTests
    : public ::testing::Test,
      public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("incremental", "true");
    s->set_opt("produce-models", "true");
    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
  }
  SmtSolver s;
  Sort boolsort, bvsort;
};

TEST_P(UnitIncrementalTests, ContextLevel)
{
  Term a = s->make_symbol("a", boolsort);
  Term b = s->make_symbol("b", boolsort);
  s->assert_formula(a);

  EXPECT_EQ(s->get_context_level(), 0);

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  s->push();
  EXPECT_EQ(s->get_context_level(), 1);
  s->assert_formula(s->make_term(Not, b));
  r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  s->push();
  EXPECT_EQ(s->get_context_level(), 2);
  s->assert_formula(s->make_term(Or, s->make_term(Not, a), b));

  r = s->check_sat();
  ASSERT_TRUE(r.is_unsat());

  s->pop();
  EXPECT_EQ(s->get_context_level(), 1);
  r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  s->pop();
  EXPECT_EQ(s->get_context_level(), 0);
  s->assert_formula(b);
  r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  s->push(5);
  EXPECT_EQ(s->get_context_level(), 5);
  s->assert_formula(s->make_term(Not, a));
  r = s->check_sat();
  ASSERT_TRUE(r.is_unsat());

  s->pop_all();
  EXPECT_EQ(s->get_context_level(), 0);
  r = s->check_sat();
  ASSERT_TRUE(r.is_sat());
}

TEST_P(UnitIncrementalTests, PopPastThePushesIsRefused)
{
  Term a = s->make_symbol("a", boolsort);
  EXPECT_THROW(s->pop(), IncorrectUsageException);
  EXPECT_EQ(s->get_context_level(), 0);

  s->push();
  s->assert_formula(a);
  EXPECT_THROW(s->pop(2), IncorrectUsageException);
  EXPECT_EQ(s->get_context_level(), 1);
  s->assert_formula(s->make_term(Not, a));
  EXPECT_TRUE(s->check_sat().is_unsat());
  s->pop();
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST_P(UnitIncrementalTests, PushMoreLevelsThanTheSolverTakes)
{
  const SolverEnum se = GetParam().solver_enum;
  if (se != BTOR && se != BZLA && se != CVC5)
  {
    GTEST_SKIP() << "This backend pushes one level at a time, so it takes "
                    "any number of levels, and pushing this many would not end";
  }
  const uint64_t levels = uint64_t{ numeric_limits<uint32_t>::max() } + 2;
  EXPECT_THROW(s->push(levels), IncorrectUsageException);
  EXPECT_EQ(s->get_context_level(), 0);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedUnitIncrementalTests,
    UnitIncrementalTests,
    testing::ValuesIn(filter_solver_configurations_with_generic({ TERMITER })));

}  // namespace
