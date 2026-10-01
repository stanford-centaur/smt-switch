#include <gtest/gtest.h>

#include <vector>

#include "cvc5/cvc5.h"

using namespace cvc5;

TEST(Cvc5InterpolantsApi, InterpolantOfConjunction)
{
  TermManager tm;
  Sort boolsort = tm.getBooleanSort();
  Term b1 = tm.mkConst(boolsort, "b1");
  Term b2 = tm.mkConst(boolsort, "b2");

  EXPECT_EQ(b2.getKind(), Kind::CONSTANT);

  Solver s(tm);
  s.setOption("produce-interpolants", "true");
  s.setOption("incremental", "false");
  s.assertFormula(tm.mkTerm(Kind::AND, { b1, b2 }));
  Term I = s.getInterpolant(b2);

  ASSERT_FALSE(I.isNull());

  // (and b1 b2) implies I, I implies b2, and b2 is the only symbol the two
  // sides share, so I must be equivalent to b2, though not necessarily b2
  // itself: its kind need not be CONSTANT
  EXPECT_TRUE(I.getSort().isBoolean());
  Solver checker(tm);
  checker.assertFormula(tm.mkTerm(Kind::DISTINCT, { I, b2 }));
  EXPECT_TRUE(checker.checkSat().isUnsat());
}
