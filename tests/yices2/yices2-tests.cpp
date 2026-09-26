/*********************                                                        */
/*! \file yices2-tests.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
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

#include <memory>
#include <vector>

#include "smt.h"
#include "yices2_factory.h"
// after a full installation
// #include "smt-switch/boolector_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;

TEST(Yices2Tests, SortsTermsAndModels)
{
  SmtSolver s = Yices2SolverFactory::create(true);
  s->set_logic("QF_ABV");
  s->set_opt("produce-models", "true");
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term y = s->make_symbol("y", bvsort8);
  Term z = s->make_symbol("z", bvsort8);
  s->make_term(true);
  EXPECT_NE(x, y);
  Term x_copy = x;
  EXPECT_EQ(x, x_copy);

  // check sorts
  Sort xsort = x->get_sort();
  Sort ysort = y->get_sort();
  EXPECT_EQ(xsort, ysort);

  Sort arr_sort = s->make_sort(ARRAY, s->make_sort(BV, 4), bvsort8);
  EXPECT_NE(xsort, arr_sort);
  EXPECT_NE(xsort, arr_sort->get_indexsort());
  EXPECT_EQ(xsort, arr_sort->get_elemsort());

  Term xpy = s->make_term(BVAdd, x, y);
  Term z_eq_xpy = s->make_term(Equal, z, xpy);

  EXPECT_TRUE(x->is_symbolic_const());
  EXPECT_FALSE(xpy->is_symbolic_const());

  Op ext30 = Op(Extract, 3, 0);
  Term x_lower = s->make_term(ext30, x);
  Term x_ext = s->make_term(Op(Zero_Extend, 4), x_lower);

  Sort funsort =
      s->make_sort(FUNCTION, SortVec{ x_lower->get_sort(), x->get_sort() });
  Term uf = s->make_symbol("f", funsort);
  Term uf_app = s->make_term(Apply, uf, x_lower);
  EXPECT_EQ(uf_app->get_op(), Apply);
  EXPECT_EQ(uf->get_sort(), funsort);
  EXPECT_NE(uf->get_sort(), uf_app->get_sort());

  s->assert_formula(z_eq_xpy);
  s->assert_formula(s->make_term(BVUlt, x, s->make_term(4, bvsort8)));
  s->assert_formula(s->make_term(BVUlt, y, s->make_term(4, bvsort8)));
  s->assert_formula(s->make_term(BVUgt, z, s->make_term("5", bvsort8)));
  // This is actually a redundant assertion -- just testing
  s->assert_formula(s->make_term(Equal, x_ext, x));
  s->assert_formula(s->make_term(Distinct, x, z));
  s->assert_formula(s->make_term(BVUle, uf_app, s->make_term(3, bvsort8)));
  s->assert_formula(
      s->make_term(BVUge, uf_app, s->make_term("00000011", bvsort8, 2)));

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  EXPECT_EQ(s->get_value(x)->to_int(), 3);
  EXPECT_EQ(s->get_value(y)->to_int(), 3);
  EXPECT_EQ(s->get_value(z)->to_int(), 6);
  EXPECT_EQ(s->get_value(x_ext)->to_int(), 3);
  EXPECT_EQ(s->get_value(x_lower)->to_int(), 3);
  EXPECT_EQ(s->get_value(uf_app)->to_int(), 3);
}
