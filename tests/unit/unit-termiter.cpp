/*********************                                                        */
/*! \file unit-termiter.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for term iteration.
**
**
**/

#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"
#include "identity_walker.h"

using namespace smt;
using namespace std;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTests);
class UnitTests : public ::testing::Test,
                  public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  }
  SmtSolver s;
  Sort bvsort, funsort, arrsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ConstArrUnitTests);
class ConstArrUnitTests : public UnitTests
{
};

TEST_P(UnitTests, TermIter)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  TermIter it = fx->begin();
  TermIter it2;
  it2 = it;

  EXPECT_EQ(it, it);
  EXPECT_EQ(it, it2);
}

TEST_P(ConstArrUnitTests, ConstArr)
{
  Term zero     = s->make_term(0, bvsort);
  Term constarr = s->make_term(zero, arrsort);
  ASSERT_TRUE(constarr->get_op().is_null());
  ASSERT_TRUE(constarr->get_sort() == arrsort);
  ASSERT_TRUE(constarr->get_sort()->get_indexsort() == bvsort);
  ASSERT_TRUE(constarr->get_sort()->get_elemsort() == bvsort);
}

TEST_P(ConstArrUnitTests, IdentityWalker)
{
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term arr = s->make_symbol("arr", arrsort);
  Term f = s->make_symbol("f", funsort);

  Term fx = s->make_term(Apply, f, x);
  Term ypfx = s->make_term(BVAdd, y, fx);
  Term xmy = s->make_term(BVMul, y, x);
  Term shift = s->make_term(BVShl, xmy, ypfx);
  Term constarr = s->make_term(s->make_term(0, bvsort), arrsort);

  Term store_0 = s->make_term(Store, constarr, x, xmy);
  Term store_1 = s->make_term(Store, store_0, y, shift);
  Term final_term = s->make_term(Select, store_1, ypfx);

  IdentityWalker iw(s, false); // don't clear the cache between calls
  Term id_final_term = iw.visit(final_term);
  ASSERT_EQ(final_term, id_final_term);
}

TEST_P(UnitTests, InputIterator)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);
  TermVec children(fx->begin(), fx->end());
  ASSERT_EQ(children[0], f);
  ASSERT_EQ(children[1], x);
}

TEST_P(UnitTests, CopyIter)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  Term v = s->make_symbol("v", bvsort);
  Term fv = s->make_term(Apply, f, v);

  ASSERT_NE(fx, fv);

  TermIter it1 = fx->begin();
  TermIter it2 = fx->begin();
  EXPECT_EQ(it1, it2);
  TermIter it3 = fv->begin();
  EXPECT_NE(it1, it3);
  it2 = it3;
  EXPECT_NE(it1, it2);
}

INSTANTIATE_TEST_SUITE_P(ParametrizedUnit,
                         UnitTests,
                         testing::ValuesIn(filter_solver_configurations({ TERMITER })));

INSTANTIATE_TEST_SUITE_P(
    ParametrizedConstArrUnit,
    ConstArrUnitTests,
    testing::ValuesIn(filter_solver_configurations({ CONSTARR, TERMITER })));

}  // namespace smt_tests
