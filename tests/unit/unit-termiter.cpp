#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

// collect all the available solvers
std::vector<SolverEnum> collect_solver_enums()
{
  std::vector<SolverEnum> solver_enums;

  for (auto elem : available_solvers())
  {
    solver_enums.push_back(elem.first);
  }

  return solver_enums;
}

// full support
std::vector<SolverEnum> full_support_enums()
{
  std::vector<SolverEnum> solver_enums;
  for (auto elem : available_solvers())
  {
    // TODO: Finish CVC4 back implementation
    if (elem.first != CVC4)
    {
      solver_enums.push_back(elem.first);
    }
  }
  return solver_enums;
}

class UnitTests : public ::testing::Test,
                  public testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = available_solvers().at(GetParam())();

    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  }
  SmtSolver s;
  Sort bvsort, funsort, arrsort;
};


class FullSupportUnitTests : public ::testing::Test,
                             public testing::WithParamInterface<SolverEnum>
{
protected:
  void SetUp() override
  {
    s = available_solvers().at(GetParam())();

    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  }
  SmtSolver s;
  Sort bvsort, funsort, arrsort;
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

TEST_P(FullSupportUnitTests, ConstArr)
{
  Term zero     = s->make_term(0, bvsort);
  Term constarr = s->make_term(zero, arrsort);
  ASSERT_TRUE(constarr->get_op().is_null());
  ASSERT_TRUE(constarr->get_sort() == arrsort);
  ASSERT_TRUE(constarr->get_sort()->get_indexsort() == bvsort);
  ASSERT_TRUE(constarr->get_sort()->get_elemsort() == bvsort);
}

INSTANTIATE_TEST_SUITE_P(ParametrizedForwardOnlyUnit,
                         UnitTests,
                         testing::ValuesIn(collect_solver_enums()));

INSTANTIATE_TEST_SUITE_P(ParametrizedFullSupportUnit,
                         FullSupportUnitTests,
                         testing::ValuesIn(full_support_enums()));

}  // namespace smt_tests
