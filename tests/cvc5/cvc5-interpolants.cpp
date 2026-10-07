/***************************************************************************/
/*! \file cvc5-interpolants.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
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

#include "cvc5_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/cvc5_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;

TEST(Cvc5Interpolants, InterpolatesAfterResetAssertions)
{
  SmtInterpolator s = Cvc5SolverFactory::create_interpolating_solver();
  Sort intsort = s->make_sort(INT);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);
  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  Term B = s->make_term(Gt, x, z);
  // a reset before first query as well as after one
  s->reset_assertions();
  for (int round = 0; round < 2; ++round)
  {
    Term I;
    EXPECT_TRUE(s->get_interpolant(A, B, I).is_unsat()) << "round " << round;
    EXPECT_TRUE(I) << "round " << round;
    s->reset_assertions();
  }
}

TEST(Cvc5Interpolants, GetInterpolant)
{
  SmtInterpolator s = Cvc5SolverFactory::create_interpolating_solver();
  Sort intsort = s->make_sort(INT);

  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  // x=0
  Term x_eq_0 = s->make_term(Equal, x, s->make_term(0, intsort));
  EXPECT_THROW(s->assert_formula(x_eq_0), IncorrectUsageException);

  // x<y /\ y<z
  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  // x<z
  Term B = s->make_term(Gt, x, z);
  Term I;
  Result r = s->get_interpolant(A, B, I);
  EXPECT_TRUE(r.is_unsat());

  // try getting a second interpolant with different A and B
  A = s->make_term(And, s->make_term(Gt, x, y), s->make_term(Gt, y, z));
  B = s->make_term(Lt, x, z);
  r = s->get_interpolant(A, B, I);
  EXPECT_TRUE(r.is_unsat());

  // now try a satisfiable formula
  r = s->get_interpolant(A, s->make_term(Gt, x, z), I);
  EXPECT_FALSE(r.is_unsat());
}

// x < y < z against x > z has an interpolant
static void expect_interpolant(const SmtInterpolator & s)
{
  Sort intsort = s->make_sort(INT);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);
  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  Term B = s->make_term(Gt, x, z);
  Term I;
  EXPECT_TRUE(s->get_interpolant(A, B, I).is_unsat());
  EXPECT_TRUE(I);
}

TEST(Cvc5Interpolants, RefusesTurningInterpolationOff)
{
  SmtInterpolator s = Cvc5SolverFactory::create_interpolating_solver();
  EXPECT_THROW(s->set_opt("produce-interpolants", "false"),
               IncorrectUsageException);
  expect_interpolant(s);
}
