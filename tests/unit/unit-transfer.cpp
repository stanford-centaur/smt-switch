/*!
 * \file unit-transfer.cpp
 * \brief Unit tests for transferring terms between solvers
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <memory>
#include <string>
#include <unordered_set>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/term_translator.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTransferTests);
class UnitTransferTests
    : public ::testing::Test,
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitQuantifierTransferTests);
class UnitQuantifierTransferTests : public UnitTransferTests
{
};

// TODO: Eventually test transferring terms between each pair of solvers

TEST_P(UnitTransferTests, SimpleUFTransfer)
{
  Term a = s->make_symbol("a", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fa = s->make_term(Apply, f, a);

  SmtSolver s2 = create_solver(GetParam());
  TermTranslator tr(s2);

  Term f2 = tr.transfer_term(f);
  Term a2 = tr.transfer_term(a);
  Term fa_2 = tr.transfer_term(fa);

  TermVec children(fa_2->begin(), fa_2->end());
  ASSERT_EQ(children.size(), 2);
  EXPECT_EQ(f2, children[0]);
  EXPECT_EQ(a2, children[1]);
}

TEST_P(UnitTransferTests, MonotonicUF)
{
  Term x = s->make_param("x", bvsort);
  Term y = s->make_param("y", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);
  Term fy = s->make_term(Apply, f, y);

  Term free_x_le_y = s->make_term(BVUle, x, y);
  Term free_fx_le_fy = s->make_term(BVUle, fx, fy);
  Term fx_le_fy =
      s->make_term(Forall, { x }, s->make_term(Forall, { y }, free_fx_le_fy));

  SmtSolver s2 = create_solver(GetParam());
  TermTranslator tr(s2);

  // EXPECT_NO_THROW(tr.transfer_term(fx_le_fy));
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedTransferUnit,
    UnitTransferTests,
    testing::ValuesIn(filter_non_generic_solver_configurations(
        { FULL_TRANSFER, QUANTIFIERS })));

}  // namespace
