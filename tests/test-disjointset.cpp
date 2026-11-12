/*!
 * \file test-disjointset.cpp
 * \brief Tests for disjoint-set
 * \author Ahmed Irfan
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/utils.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(DisjointSetTests);
class DisjointSetTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    bvsort = s->make_sort(BV, 8);
    x = s->make_symbol("x", bvsort);
    y = s->make_symbol("y", bvsort);
    z = s->make_symbol("z", bvsort);
    w = s->make_symbol("w", bvsort);
  }
  SmtSolver s;
  Sort bvsort;
  Term x, y, z, w;
};

static bool disjoint_set_rank(const Term & t1, const Term & t2)
{
  if (!t1->is_value() && !t2->is_value())
  {
    return t1 < t2;
  }
  return !t1->is_value();
}

TEST_P(DisjointSetTests, TestDisjointSet)
{
  Term t1, t2, t3, t4;
  DisjointSet ds(disjoint_set_rank);

  ds.add(z, y);
  t1 = ds.find(y);
  t2 = ds.find(z);
  EXPECT_TRUE(t1 == t2);

  ds.add(x, y);
  t3 = ds.find(x);
  EXPECT_TRUE(t1 == t3);

  ds.add(w, z);
  t4 = ds.find(w);
  EXPECT_TRUE(t1 == t4);
}

TEST_P(DisjointSetTests, FindRefusesTermNeverAdded)
{
  DisjointSet ds(disjoint_set_rank);
  ds.add(z, y);
  EXPECT_THROW(ds.find(x), IncorrectUsageException);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverDisjointSetTests,
                         DisjointSetTests,
                         testing::ValuesIn(available_solver_configurations()));

}  // namespace
