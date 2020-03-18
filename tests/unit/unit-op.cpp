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

TEST_P(UnitTests, FunOp)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  ASSERT_EQ(fx->get_op(), Apply);
}

TEST_P(UnitTests, IndexedOps1)
{
  Term x = s->make_symbol("x", bvsort);
  Op ext = Op(Extract, 2, 0);
  Term ext_x = s->make_term(ext, x);
  ASSERT_EQ(ext_x->get_op(), ext);

  Op rep = Op(Repeat, 2);
  Term rep_x = s->make_term(rep, x);
  // some solvers rewrite -- might be concats
  // but we can check the sort
  ASSERT_EQ(rep_x->get_sort()->get_width(), 8);

  Op se = Op(Sign_Extend, 4);
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

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnit,
                         UnitTests,
                         testing::ValuesIn(available_termiter_solver_enums()));

}  // namespace smt_tests
