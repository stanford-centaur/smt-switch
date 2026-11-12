/*!
 * \file unit-term-hashtable.cpp
 * \brief Unit tests for term hashtable
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <memory>
#include <string>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term_hashtable.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTestsHashTable);
class UnitTestsHashTable : public testing::Test,
                           public testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    // need to make sure we're not using a LoggingSolver
    // otherwise the reference counts of terms will be influenced
    // thus, use the "lite" solvers
    SolverEnum se = GetParam();
    SolverConfiguration sc(se, false);
    s = create_solver(sc);

    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  }
  SmtSolver s;
  Sort bvsort, funsort, arrsort;
  TermHashTable table;
};

TEST_P(UnitTestsHashTable, HashTable)
{
  Term x = s->make_symbol("x", bvsort);
  Term one = s->make_term(1, bvsort);
  Term xp1 = s->make_term(BVAdd, x, one);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);
  Term fxeqxp1 = s->make_term(Equal, fx, xp1);

  Term xp1_2 = s->make_term(BVAdd, x, one);
  Term cp_xp1_2 = xp1_2;
  ASSERT_EQ(xp1_2.use_count(), 2);
  ASSERT_EQ(cp_xp1_2.use_count(), 2);
  ASSERT_NE(xp1.get(), xp1_2.get());
  ASSERT_FALSE(table.lookup(xp1));

  table.insert(xp1);
  ASSERT_TRUE(table.lookup(xp1_2));
  ASSERT_EQ(xp1.get(), xp1_2.get());
  ASSERT_EQ(xp1_2.use_count(),
            3);  // two references here and one in the hash table
  ASSERT_EQ(cp_xp1_2.use_count(), 1);
}

// similarly to logging solvers, generic solvers
// increase the usage count and so we ignore
// them in this test
INSTANTIATE_TEST_SUITE_P(
    ParametrizedUnitHashTable,
    UnitTestsHashTable,
    testing::ValuesIn(available_non_generic_solver_enums()));

}  // namespace
