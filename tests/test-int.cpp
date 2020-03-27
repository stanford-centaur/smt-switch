#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class IntTests : public ::testing::Test,
                 public ::testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = available_solvers().at(GetParam())();
    s->set_opt("produce-models", "true");
    intsort = s->make_sort(INT);
  }
  SmtSolver s;
  Sort intsort;
};

TEST_P(IntTests, IntDiv)
{
  Term five = s->make_term(5, intsort);
  Term two = s->make_term(2, intsort);
  Term res = s->make_symbol("res", intsort);
  Term div = s->make_term(IntDiv, five, two);
  s->assert_formula(s->make_term(Equal, res, div));
  s->check_sat();
  Term resval = s->get_value(res);
  ASSERT_EQ(resval, two);
}

TEST_P(IntTests, NegValue)
{
  Term one = s->make_term(1, intsort);
  ASSERT_TRUE(one->is_value());
  Term neg_one = s->make_term(Negate, one);
  ASSERT_FALSE(neg_one->is_value());
  int num_children = 0;
  for (auto c : neg_one)
  {
    num_children++;
  }
  ASSERT_EQ(num_children, 1);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverIntTests,
                         IntTests,
                         testing::ValuesIn(available_int_solver_enums()));

}  // namespace smt_tests
