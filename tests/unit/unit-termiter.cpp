#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class UnitTests : public ::testing::Test,
                  public testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = available_solvers().at(GetParam())();

    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
  }
  SmtSolver s;
  Sort bvsort, funsort;
};

TEST_P(UnitTests, TermIter)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  TermIter it = fx->begin();
  TermIter it2;
  it2 = it;

  ASSERT_TRUE(it == it2);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnit,
                         UnitTests,
                         testing::ValuesIn(available_solver_enums()));

}  // namespace smt_tests
