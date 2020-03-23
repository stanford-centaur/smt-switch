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
    // IMPORTANT : make sure not to use doubly nested LoggingSolvers
    // can mess things up
    // Thus, need to use the "lite" version of solvers
    // before wrapping with a LoggingSolver
    s = make_shared<LoggingSolver>(available_lite_solvers().at(GetParam())());
    s->set_opt("produce-models", "true");
    bvsort4 = s->make_sort(BV, 4);
    bvsort8 = s->make_sort(BV, 8);
    arraysort = s->make_sort(ARRAY, bvsort4, bvsort8);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort4, bvsort8 });

    x = s->make_symbol("x", bvsort4);
    y = s->make_symbol("y", bvsort4);
    zero = s->make_term(0, bvsort4);
    one = s->make_term(1, bvsort4);
  }
  SmtSolver s;
  Sort bvsort4, bvsort8, arraysort, funsort;
  Term x, y, zero, one;
};

TEST_P(LoggingTests, Children)
{
  ASSERT_TRUE(x->get_op().is_null());
  ASSERT_TRUE(y->is_symbolic_const());
  ASSERT_FALSE(y->is_value());

  Term xp1 = s->make_term(BVAdd, x, one);
  ASSERT_EQ(xp1->get_op(), BVAdd);
  TermVec children;
  for (auto tt : xp1)
  {
    children.push_back(tt);
  }
  ASSERT_EQ(children[0], x);
  ASSERT_EQ(children[1], one);
}

TEST_P(LoggingTests, HashConsing)
{
  Term xp1 = s->make_term(BVAdd, x, one);
  // Check hash-consing using comparison of underlying pointers
  Term xp1_2 = s->make_term(BVAdd, x, one);
  ASSERT_EQ(xp1.get(), xp1_2.get());
}

TEST_P(LoggingTests, Sorts)
{
  Term cond = s->make_term(BVUge, x, zero);
  ASSERT_EQ(cond->get_sort()->get_sort_kind(), BOOL);
  Term relu = s->make_term(Ite, cond, x, zero);
  ASSERT_EQ(relu->get_sort(), x->get_sort());
}

TEST_P(LoggingTests, ConstantSorts)
{
  Term t = s->make_term(true);
  Term f = s->make_term(false);
  ASSERT_NE(t, f);
  ASSERT_EQ(t, t);

  Sort bvsort1 = s->make_sort(BV, 1);
  Term bv0 = s->make_term(0, bvsort1);
  Term bv1 = s->make_term(1, bvsort1);
  ASSERT_NE(bv0, bv1);
  ASSERT_EQ(bv1, bv1);

  ASSERT_NE(f, bv0);
  ASSERT_NE(f, bv1);
  ASSERT_NE(t, bv0);
  ASSERT_NE(t, bv1);

  ASSERT_EQ(t->get_sort()->get_sort_kind(), BOOL);
  ASSERT_EQ(bv0->get_sort()->get_sort_kind(), BV);
  ASSERT_EQ(bv1->get_sort()->get_width(), 1);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverLoggingTests,
                         LoggingTests,
                         testing::ValuesIn(available_solver_enums()));

}  // namespace smt_tests
