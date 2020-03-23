#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"
#include "term_hashtable.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class UnitTestsHashTable : public testing::Test,
                           public testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    // need to make sure we're not using a LoggingSolver
    // otherwise the reference counts of terms will be influenced
    // thus, use the "lite" solvers
    s = available_lite_solvers().at(GetParam())();

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

INSTANTIATE_TEST_SUITE_P(ParametrizedUnitHashTable,
                         UnitTestsHashTable,
                         testing::ValuesIn(available_solver_enums()));

}  // namespace smt_tests
