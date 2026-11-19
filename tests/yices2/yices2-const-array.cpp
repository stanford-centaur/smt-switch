/*!
 * \file yices2-const-array.cpp
 * \brief Tests the constant arrays Yices2 can build and read
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Yices2 does not claim CONSTARR, since its context refuses a constant
 * array that reaches it, but make_term still builds one, and reading an
 * index out of it works.
 */
#include <gtest/gtest.h>

#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/yices2_factory.h"

namespace smt::tests {

namespace {

class Yices2ConstArray : public testing::Test
{
 protected:
  void SetUp() override
  {
    s = Yices2SolverFactory::create(false);
    bvsort4 = s->make_sort(SortKind::BV, 4);
    bvsort8 = s->make_sort(SortKind::BV, 8);
    arrsort = s->make_sort(SortKind::ARRAY, bvsort4, bvsort8);
    zero = s->make_term(0, bvsort8);
    const_arr = s->make_term(zero, arrsort);
  }
  SmtSolver s;
  Sort bvsort4, bvsort8, arrsort;
  Term zero, const_arr;
};

TEST_F(Yices2ConstArray, IsValueWithBaseChild)
{
  EXPECT_TRUE(const_arr->is_value());
  EXPECT_FALSE(const_arr->is_symbolic_const());
  EXPECT_TRUE(const_arr->get_op().is_null());
  for (const Term & c : const_arr)
  {
    EXPECT_EQ(c, zero);
  }
}

TEST_F(Yices2ConstArray, SameBaseIsSameTerm)
{
  EXPECT_EQ(s->make_term(zero, arrsort), const_arr);
}

TEST_F(Yices2ConstArray, ReadGivesTheBase)
{
  Term idx = s->make_symbol("idx", bvsort4);
  s->assert_formula(s->make_term(
      Op::Distinct, s->make_term(Op::Select, const_arr, idx), zero));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

}  // namespace

}  // namespace smt::tests
