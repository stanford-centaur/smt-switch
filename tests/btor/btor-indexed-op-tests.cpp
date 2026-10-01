/*********************                                                        */
/*! \file btor-indexed-op-tests.cpp
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

TEST(BtorIndexedOps, RotateExtractRepeat)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("produce-models", "true");
  Sort bvsort9 = s->make_sort(BV, 9);
  Term x = s->make_symbol("x", bvsort9);
  Term y = s->make_symbol("y", bvsort9);
  Term onebit = s->make_symbol("onebit", s->make_sort(BV, 1));

  Term unnecessary_rotation = s->make_term(Op(Rotate_Right, 1), onebit);

  Op ext74 = Op(Extract, 7, 4);
  Term x_upper = s->make_term(ext74, x);

  Term y_ror = s->make_term(Op(Rotate_Right, 2), y);
  Term y_rol = s->make_term(Op(Rotate_Left, 2), y);

  s->assert_formula(s->make_term(Equal, y_ror, y_rol));
  s->assert_formula(s->make_term(Distinct, y, s->make_term(0, bvsort9)));
  s->assert_formula(s->make_term(
      Equal, x, s->make_term(Op(Repeat, 9), unnecessary_rotation)));

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  // ror 2 = rol 2 makes rotating by 4 the identity, which on 9 bits forces
  // all bits of y to be equal
  EXPECT_EQ(s->get_value(y)->to_int(), 0b1'1111'1111);
  // x repeats one bit 9 times, so x and x_upper are all zeros or all ones
  auto x_val = s->get_value(x)->to_int();
  EXPECT_TRUE(x_val == 0 || x_val == 0b1'1111'1111);
  EXPECT_EQ(s->get_value(x_upper)->to_int(),
            x_val == 0b1'1111'1111 ? 0b1111 : 0);
}
