/*********************                                                        */
/*! \file cvc5-term-iter.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
**
**
**/

#include <vector>

#include "cvc5/cvc5.h"
#include "assert.h"
#include "cvc5_term.h"
#include "gtest/gtest.h"

using namespace smt;
using namespace std;

TEST(Cvc5TermIterTest, Copy)
{
  ::cvc5::TermManager term_manager;
  ::cvc5::Sort bvsort4 = term_manager.mkBitVectorSort(4);
  ::cvc5::Sort funsort = term_manager.mkFunctionSort({ bvsort4 }, bvsort4);

  ::cvc5::Term x = term_manager.mkConst(bvsort4, "x");
  ::cvc5::Term v = term_manager.mkConst(bvsort4, "v");
  ::cvc5::Term f = term_manager.mkConst(funsort, "f");

  ::cvc5::Term fx = term_manager.mkTerm(cvc5::Kind::APPLY_UF, { f, x });
  ::cvc5::Term fv = term_manager.mkTerm(cvc5::Kind::APPLY_UF, { f, v });

  Cvc5TermIter it1(fx, 0);
  Cvc5TermIter it2(fx, 0);

  // NOTE: can't use _EQ and _NE macros because
  // it takes a const argument
  EXPECT_TRUE(it1 == it2);

  ++it2;
  EXPECT_TRUE(it1 != it2);

  Cvc5TermIter it3(fv, 0);
  EXPECT_TRUE(it1 != it3);

  Cvc5TermIter it4(it3);
  EXPECT_TRUE(it3 == it4);
  EXPECT_TRUE(it1 != it4);
}
