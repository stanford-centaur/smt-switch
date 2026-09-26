/*********************                                                        */
/*! \file yices2-indexed-op-tests.cpp
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
// #include "smt-switch/yices2_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;

TEST(Yices2IndexedOps, RotateExtractRepeat)
{
  SmtSolver s = Yices2SolverFactory::create(true);
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

  EXPECT_EQ(y_ror->to_string(), "((_ rotate_right 2) y)");
  EXPECT_EQ(y_rol->to_string(), "((_ rotate_left 2) y)");

  s->assert_formula(s->make_term(Equal, y_ror, y_rol));
  s->assert_formula(s->make_term(Distinct, y, s->make_term(0, bvsort9)));
  s->assert_formula(s->make_term(
      Equal, x, s->make_term(Op(Repeat, 9), unnecessary_rotation)));

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  // ror 2 = rol 2 makes y invariant under rotation by 4, which on 9 bits
  // (gcd(4, 9) = 1) makes all its bits equal; y != 0, so y is all ones
  EXPECT_EQ(s->get_value(y)->to_int(), 0b1'1111'1111);
  // x repeats one bit nine times, so it and its slice x_upper are all zeros
  // or all ones
  auto x_val = s->get_value(x)->to_int();
  EXPECT_TRUE(x_val == 0 || x_val == 0b1'1111'1111) << x_val;
  EXPECT_EQ(s->get_value(x_upper)->to_int(),
            x_val == 0b1'1111'1111 ? 0b1111u : 0u);
}
