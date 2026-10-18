/*!
 * \file msat-array-values.cpp
 * \brief Tests that MathSAT's get_array_values refuses what it cannot read.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include <gtest/gtest.h>

#include "msat_factory.h"
#include "smt.h"

using namespace smt;

class MsatArrayValues : public testing::Test
{
 protected:
  void SetUp() override
  {
    s = MsatSolverFactory::create(false);
    s->set_logic("QF_ABV");
    s->set_opt("produce-models", "true");
    Sort bvsort = s->make_sort(BV, 8);
    x = s->make_symbol("x", bvsort);
    arr = s->make_symbol("arr", s->make_sort(ARRAY, bvsort, bvsort));
  }

  SmtSolver s;
  Term x;
  Term arr;
};

TEST_F(MsatArrayValues, NonArrayRefused)
{
  s->assert_formula(s->make_term(
      Equal, s->make_term(Select, arr, x), s->make_term(1, x->get_sort())));
  ASSERT_TRUE(s->check_sat().is_sat());
  Term const_base;
  EXPECT_THROW(s->get_array_values(x, const_base), IncorrectUsageException);
}

TEST_F(MsatArrayValues, WithoutCheckSatRefused)
{
  Term const_base;
  EXPECT_THROW(s->get_array_values(arr, const_base), IncorrectUsageException);
}
