/*********************                                                        */
/*! \file msat-int-arithmetic.cpp
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

#include <cstdint>
#include <memory>
#include <vector>

#include "msat_factory.h"
#include "smt.h"
// after full installation
// #include "smt-switch/msat_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;

TEST(MsatIntArithmetic, NonlinearConstraints)
{
  SmtSolver s = MsatSolverFactory::create(false);
  s->set_opt("produce-models", "true");
  s->set_logic("QF_NIA");
  Sort intsort = s->make_sort(INT);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  s->assert_formula(s->make_term(Ge, x, y));
  s->assert_formula(s->make_term(Le, z, s->make_term(Plus, x, y)));
  s->assert_formula(
      s->make_term(Lt, s->make_term(Negate, z), s->make_term(Minus, x, y)));
  s->assert_formula(
      s->make_term(Gt, s->make_term(Minus, x, y), s->make_term(Mult, x, y)));

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  // the model is not unique, so check that it satisfies the constraints
  int64_t xv = s->get_value(x)->to_signed_int();
  int64_t yv = s->get_value(y)->to_signed_int();
  int64_t zv = s->get_value(z)->to_signed_int();
  EXPECT_GE(xv, yv);
  EXPECT_LE(zv, xv + yv);
  EXPECT_LT(-zv, xv - yv);
  EXPECT_GT(xv - yv, xv * yv);
}
