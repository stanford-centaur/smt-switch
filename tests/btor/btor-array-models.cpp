/*********************                                                        */
/*! \file btor-array-models.cpp
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

#include <memory>
#include <vector>

#include "boolector_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/boolector_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

TEST(BtorArrayModels, GetArrayValues)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("produce-models", "true");
  Sort bvsort32 = s->make_sort(BV, 32);
  Sort array32_32 = s->make_sort(ARRAY, bvsort32, bvsort32);
  Term x0 = s->make_symbol("x0", bvsort32);
  Term x1 = s->make_symbol("x1", bvsort32);
  Term y = s->make_symbol("y", bvsort32);
  Term arr = s->make_symbol("arr", array32_32);

  Term constraint = s->make_term(Equal, s->make_term(Select, arr, x0), x1);
  constraint = s->make_term(
      And, constraint, s->make_term(Equal, s->make_term(Select, arr, x1), y));
  constraint = s->make_term(And, constraint, s->make_term(Distinct, x1, y));
  s->assert_formula(constraint);
  Result r = s->check_sat();

  ASSERT_TRUE(r.is_sat());

  Term x0_val = s->get_value(x0);
  Term x1_val = s->get_value(x1);
  Term y_val = s->get_value(y);
  EXPECT_EQ(s->get_value(s->make_term(Select, arr, x0)), x1_val);
  EXPECT_EQ(s->get_value(s->make_term(Select, arr, x1)), y_val);
  EXPECT_NE(x1_val, y_val);

  // x0 and x1 must differ (else x1 = arr[x1] = y), and the model reads arr
  // at both, so the array assignment lists both indices
  Term out_const_base;
  UnorderedTermMap arr_map = s->get_array_values(arr, out_const_base);
  ASSERT_EQ(arr_map.count(x0_val), 1);
  EXPECT_EQ(arr_map.at(x0_val), x1_val);
  ASSERT_EQ(arr_map.count(x1_val), 1);
  EXPECT_EQ(arr_map.at(x1_val), y_val);
}
