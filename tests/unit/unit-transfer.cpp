#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class UnitTransferTests : public ::testing::Test,
                          public ::testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = available_solvers().at(GetParam())();

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
  }
  SmtSolver s;
  Sort boolsort, bvsort, funsort;
};

// TODO: Eventually test transferring terms between each pair of solvers

TEST_P(UnitTransferTests, SimpleUFTransfer)
{
  Term a = s->make_symbol("a", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fa = s->make_term(Apply, f, a);

  SmtSolver s2 = available_solvers().at(GetParam())();
  TermTranslator tr(s2);

  Term f2 = tr.transfer_term(f);
  Term a2 = tr.transfer_term(a);
  Term fa_2 = tr.transfer_term(fa);

  TermVec children(fa_2->begin(), fa_2->end());
  ASSERT_EQ(children.size(), 2);
  ASSERT_EQ(f2, children[0]);
  ASSERT_EQ(a2, children[1]);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedTransferUnit,
    UnitTransferTests,
    testing::ValuesIn(available_full_transfer_solver_enums()));

}  // namespace smt_tests
