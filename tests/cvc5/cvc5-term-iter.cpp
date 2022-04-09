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

#include <iostream>
#include <memory>
#include <vector>

#include "api/cpp/cvc5.h"
#include "assert.h"
#include "cvc5_term.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

TEST(Cvc5TermIterTest, Copy)
{
  ::cvc5::Solver solver;
  ::cvc5::Sort bvsort4 = solver.mkBitVectorSort(4);
  ::cvc5::Sort funsort = solver.mkFunctionSort({bvsort4}, bvsort4);

  ::cvc5::Term x = solver.mkConst(bvsort4, "x");
  ::cvc5::Term v = solver.mkConst(bvsort4, "v");
  ::cvc5::Term f = solver.mkConst(funsort, "f");

  ::cvc5::Term fx = solver.mkTerm(cvc5::APPLY_UF, {f, x});
  ::cvc5::Term fv = solver.mkTerm(cvc5::APPLY_UF, {f, v});

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
