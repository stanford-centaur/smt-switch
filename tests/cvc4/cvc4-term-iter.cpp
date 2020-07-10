/*********************                                                        */
/*! \file cvc4-term-iter.cpp
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
#include "assert.h"

#include "gtest/gtest.h"

#include "api/cvc4cpp.h"

#include "cvc4_term.h"
#include "smt.h"

using namespace smt;
using namespace std;

TEST(CVC4TermIterTest, Copy)
{
  ::CVC4::api::Solver solver;
  ::CVC4::api::Sort bvsort4 = solver.mkBitVectorSort(4);
  ::CVC4::api::Sort funsort = solver.mkFunctionSort(bvsort4, bvsort4);

  ::CVC4::api::Term x = solver.mkConst(bvsort4, "x");
  ::CVC4::api::Term v = solver.mkConst(bvsort4, "v");
  ::CVC4::api::Term f = solver.mkConst(funsort, "f");

  ::CVC4::api::Term fx = solver.mkTerm(CVC4::api::APPLY_UF, f, x);
  ::CVC4::api::Term fv = solver.mkTerm(CVC4::api::APPLY_UF, f, v);

  CVC4TermIter it1(fx, 0);
  CVC4TermIter it2(fx, 0);

  // NOTE: can't use _EQ and _NE macros because
  // it takes a const argument
  EXPECT_TRUE(it1 == it2);

  ++it2;
  EXPECT_TRUE(it1 != it2);

  CVC4TermIter it3(fv, 0);
  EXPECT_TRUE(it1 != it3);

  CVC4TermIter it4(it3);
  EXPECT_TRUE(it3 == it4);
  EXPECT_TRUE(it1 != it4);
}
