/*!
 * \file cvc5-interpolants-api.cpp
 * \brief Tests the interpolant cvc5's own API gives for a conjunction
 * \author Yoni Zohar
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <cvc5/cvc5.h>
#include <gtest/gtest.h>

#include <string>
#include <vector>

namespace smt::tests {

namespace {

TEST(Cvc5InterpolantsApi, InterpolantOfConjunction)
{
  cvc5::TermManager tm;
  cvc5::Sort boolsort = tm.getBooleanSort();
  cvc5::Term b1 = tm.mkConst(boolsort, "b1");
  cvc5::Term b2 = tm.mkConst(boolsort, "b2");

  EXPECT_EQ(b2.getKind(), cvc5::Kind::CONSTANT);

  cvc5::Solver s(tm);
  s.setOption("produce-interpolants", "true");
  s.setOption("incremental", "false");
  s.assertFormula(tm.mkTerm(cvc5::Kind::AND, { b1, b2 }));
  cvc5::Term I = s.getInterpolant(b2);

  ASSERT_FALSE(I.isNull());

  // (and b1 b2) implies I, I implies b2, and b2 is the only symbol the two
  // sides share, so I must be equivalent to b2, though not necessarily b2
  // itself: its kind need not be CONSTANT
  EXPECT_TRUE(I.getSort().isBoolean());
  cvc5::Solver checker(tm);
  checker.assertFormula(tm.mkTerm(cvc5::Kind::DISTINCT, { I, b2 }));
  EXPECT_TRUE(checker.checkSat().isUnsat());
}

}  // namespace

}  // namespace smt::tests
