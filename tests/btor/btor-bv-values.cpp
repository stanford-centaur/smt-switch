/*!
 * \file btor-bv-values.cpp
 * \brief Bit-vector values made from strings in Boolector.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Boolector's own string constructors ignore the sort in base 2, read a
 * minus differently in base 16 and accept malformed numerals, so the
 * backend checks the string itself.
 */

#include <gtest/gtest.h>

#include "boolector_factory.h"
#include "smt.h"

using namespace smt;

namespace {

class BtorBvValues : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    s = BoolectorSolverFactory::create(false);
    bv8 = s->make_sort(BV, 8);
  }
  SmtSolver s;
  Sort bv8;
};

TEST_F(BtorBvValues, ShortValuesAreZeroExtended)
{
  EXPECT_EQ(s->make_term("1", bv8, 2), s->make_term(1, bv8));
  EXPECT_EQ(s->make_term("1", bv8, 16), s->make_term(1, bv8));
  EXPECT_EQ(s->make_term("1", bv8, 2)->get_sort(), bv8);
}

TEST_F(BtorBvValues, NegativeValuesInEveryBase)
{
  Term minus_four = s->make_term(-4, bv8);
  EXPECT_EQ(s->make_term("-4", bv8, 10), minus_four);
  EXPECT_EQ(s->make_term("-100", bv8, 2), minus_four);
  EXPECT_EQ(s->make_term("-4", bv8, 16), minus_four);
  EXPECT_EQ(s->make_term("-1", bv8, 16), s->make_term(-1, bv8));
}

TEST_F(BtorBvValues, MalformedNumeralsThrow)
{
  EXPECT_THROW(s->make_term("abc", bv8, 10), IncorrectUsageException);
  EXPECT_THROW(s->make_term("", bv8, 10), IncorrectUsageException);
  EXPECT_THROW(s->make_term("-", bv8, 10), IncorrectUsageException);
  EXPECT_THROW(s->make_term("102", bv8, 2), IncorrectUsageException);
  EXPECT_THROW(s->make_term("fg", bv8, 16), IncorrectUsageException);
}

TEST_F(BtorBvValues, OtherBasesThrow)
{
  EXPECT_THROW(s->make_term("7", bv8, 8), IncorrectUsageException);
}

}  // namespace
