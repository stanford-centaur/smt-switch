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

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
  }
  SmtSolver s;
  Sort boolsort, bvsort, funsort;
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
}

TEST_P(UnitTests, RotateOps)
{
  Term x = s->make_symbol("x", bvsort);
  Term rotate_left = s->make_term(Op(Rotate_Left, 2), x);
  Term rotate_right = s->make_term(Op(Rotate_Right, 2), rotate_left);
  s->assert_formula(s->make_term(Distinct, x, rotate_right));
  Result r = s->check_sat();
  ASSERT_TRUE(r.is_unsat());
}

TEST_P(UnitTests, BoolFun)
{
  Term b = s->make_symbol("b", boolsort);
  Sort boolfunsort = s->make_sort(FUNCTION, SortVec{ boolsort, boolsort });
  Term f = s->make_symbol("f", boolfunsort);
  Term fb = s->make_term(Apply, f, b);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnit,
                         UnitTests,
                         testing::ValuesIn(available_solver_enums()));

}  // namespace smt_tests
