/*********************                                                        */
/*! \file cvc5_test.cpp
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

#include <gtest/gtest.h>

#include "cvc5_factory.h"
#include "smt.h"
// after full installation
// #include "smt-switch/cvc5_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;

TEST(Cvc5Test, BuildTerms)
{
  SmtSolver s = Cvc5SolverFactory::create(false);
  Term x = s->make_symbol("x", s->make_sort(BV, 8));
  Term y = s->make_symbol("y", s->make_sort(BV, 8));
  EXPECT_TRUE(x->is_symbolic_const());
  EXPECT_EQ(x->get_sort(), s->make_sort(BV, 8));
  EXPECT_NE(x, y);
  Term xpy = s->make_term(BVAdd, x, y);
  EXPECT_EQ(xpy->get_op(), BVAdd);
  EXPECT_EQ(xpy->get_sort(), s->make_sort(BV, 8));
  Term xext = s->make_term(Op(Extract, 3, 0), x);
  EXPECT_EQ(xext->get_op(), Op(Extract, 3, 0));
  EXPECT_EQ(xext->get_sort()->get_width(), 4);
  Term _true = s->make_term(true);
  EXPECT_TRUE(_true->is_value());
  EXPECT_EQ(_true->get_sort()->get_sort_kind(), BOOL);
  Term _one = s->make_term(1, s->make_sort(INT));
  EXPECT_TRUE(_one->is_value());
  EXPECT_EQ(_one->get_sort()->get_sort_kind(), INT);
  EXPECT_EQ(_one->to_int(), 1);
  Term _one_r = s->make_term("1.0", s->make_sort(REAL));
  EXPECT_TRUE(_one_r->is_value());
  EXPECT_EQ(_one_r->get_sort()->get_sort_kind(), REAL);
  Term _two_bv = s->make_term(2, s->make_sort(BV, 4));
  EXPECT_TRUE(_two_bv->is_value());
  EXPECT_EQ(_two_bv->get_sort()->get_width(), 4);
  EXPECT_EQ(_two_bv->to_int(), 2);
  Term _three_bv = s->make_term("3", s->make_sort(BV, 4));
  EXPECT_TRUE(_three_bv->is_value());
  EXPECT_EQ(_three_bv->get_sort()->get_width(), 4);
  EXPECT_EQ(_three_bv->to_int(), 3);

  TermVec xpy_children;
  for (auto c : xpy)
  {
    xpy_children.push_back(c);
  }
  // BVAdd is commutative, so only the set of children is fixed
  ASSERT_EQ(xpy_children.size(), 2);
  EXPECT_TRUE(xpy_children[0] == x || xpy_children[1] == x);
  EXPECT_TRUE(xpy_children[0] == y || xpy_children[1] == y);

  Term str_a = s->make_term("a", false, s->make_sort(STRING));
  EXPECT_TRUE(str_a->is_value());
  EXPECT_EQ(str_a->get_sort()->get_sort_kind(), STRING);
  Term wstr_b = s->make_term(L"b", s->make_sort(STRING));
  EXPECT_TRUE(wstr_b->is_value());
  EXPECT_EQ(wstr_b->get_sort()->get_sort_kind(), STRING);
  EXPECT_NE(str_a, wstr_b);
  Term t = s->make_symbol("t", s->make_sort(STRING));
  Term w = s->make_symbol("w", s->make_sort(STRING));
  EXPECT_TRUE(t->is_symbolic_const());
  EXPECT_TRUE(w->is_symbolic_const());
  Term tw = s->make_term(StrConcat, t, w);
  EXPECT_EQ(tw->get_op(), StrConcat);
  EXPECT_EQ(tw->get_sort()->get_sort_kind(), STRING);
  TermVec tw_children;
  for (auto c : tw)
  {
    tw_children.push_back(c);
  }
  // concatenation is not commutative, so the order is fixed
  EXPECT_EQ(tw_children, TermVec({ t, w }));
}
