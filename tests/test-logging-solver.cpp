#include <memory>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "logging_solver.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class LoggingTests : public ::testing::Test,
                     public ::testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = make_shared<LoggingSolver>(available_solvers().at(GetParam())());
    s->set_opt("produce-models", "true");
    bvsort4 = s->make_sort(BV, 4);
    bvsort8 = s->make_sort(BV, 8);
    arraysort = s->make_sort(ARRAY, bvsort4, bvsort8);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort4, bvsort8 });
  }
  SmtSolver s;
  Sort bvsort4, bvsort8, arraysort, funsort;
};

TEST_P(LoggingTests, RecoverStructure)
{
  Term x = s->make_symbol("x", bvsort4);
  Term y = s->make_symbol("y", bvsort4);
  ASSERT_TRUE(x->get_op().is_null());
  ASSERT_TRUE(y->is_symbolic_const());
  ASSERT_FALSE(y->is_value());

  Term one = s->make_term(1, bvsort4);
  Term xp1 = s->make_term(BVAdd, x, one);
  ASSERT_EQ(xp1->get_op(), BVAdd);
  TermVec children;
  for (auto tt : xp1)
  {
    children.push_back(tt);
  }
  ASSERT_EQ(children[0], x);
  ASSERT_EQ(children[1], one);

  // // Check hash-consing using comparison of underlying pointers
  // Term xp1_2 = s->make_term(BVAdd, x, one);
  // ASSERT_EQ(xp1.get(), xp1_2.get());
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverLoggingTests,
                         LoggingTests,
                         testing::ValuesIn(available_solver_enums()));

}  // namespace smt_tests
