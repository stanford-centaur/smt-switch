/*********************                                                        */
/*! \file msat-interpolants.cpp
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

#include "msat_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/msat_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;

TEST(MsatInterpolants, RefusesOnlyTheOptionsInterpolationNeeds)
{
  SmtInterpolator s = MsatSolverFactory::create_interpolating_solver();
  EXPECT_THROW(s->set_opt("interpolation", "false"), IncorrectUsageException);
  EXPECT_THROW(s->set_opt("theory.bv.eager", "true"), IncorrectUsageException);
  // any other option reaches MathSAT while it can still take options
  EXPECT_NO_THROW(s->set_opt("dpll.ghost_filtering", "true"));

  Sort intsort = s->make_sort(INT);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);
  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  Term B = s->make_term(Gt, x, z);
  Term I;
  EXPECT_TRUE(s->get_interpolant(A, B, I).is_unsat());
  EXPECT_TRUE(I);

  // building terms created the environment, which fixes the configuration
  EXPECT_THROW(s->set_opt("dpll.ghost_filtering", "false"),
               IncorrectUsageException);
}

TEST(MsatInterpolants, InterpolatesWithoutReuse)
{
  SmtInterpolator s = MsatSolverFactory::create_interpolating_solver();
  EXPECT_THROW(s->set_opt("incremental", "maybe"), IncorrectUsageException);
  s->set_opt("incremental", "false");

  Sort intsort = s->make_sort(INT);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);
  Term w = s->make_symbol("w", intsort);
  // the two queries share their first formula, which reuse would keep
  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  Term I;
  EXPECT_TRUE(s->get_interpolant(A, s->make_term(Gt, x, z), I).is_unsat());
  EXPECT_TRUE(I);
  I = nullptr;
  EXPECT_TRUE(s->get_interpolant(A, s->make_term(Lt, z, x), I).is_unsat());
  EXPECT_TRUE(I);
  // and a satisfiable query still answers sat
  EXPECT_TRUE(s->get_interpolant(A, s->make_term(Lt, x, w), I).is_sat());
}

TEST(MsatInterpolants, GetInterpolant)
{
  SmtInterpolator s = MsatSolverFactory::create_interpolating_solver();
  Sort intsort = s->make_sort(INT);

  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  Term x_eq_0 = s->make_term(Equal, x, s->make_term(0, intsort));
  EXPECT_THROW(s->assert_formula(x_eq_0), IncorrectUsageException);

  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  Term B = s->make_term(Gt, x, z);
  Term I;
  Result r = s->get_interpolant(A, B, I);

  EXPECT_TRUE(r.is_unsat());

  s->reset_assertions();

  // try getting a second interpolant with different A and B
  A = s->make_term(And, s->make_term(Gt, x, y), s->make_term(Gt, y, z));
  B = s->make_term(Lt, x, z);
  r = s->get_interpolant(A, B, I);

  EXPECT_TRUE(r.is_unsat());

  // now try a satisfiable formula
  r = s->get_interpolant(A, s->make_term(Gt, x, z), I);
  EXPECT_TRUE(r.is_sat());
}

TEST(MsatInterpolants, InterpolatesAfterReset)
{
  SmtInterpolator s = MsatSolverFactory::create_interpolating_solver();
  // a reset before first use as well as after a query
  s->reset();
  for (int round = 0; round < 2; ++round)
  {
    {
      // the terms must go before reset() destroys their environment
      // x + y = 3 and y = 1 against x = 5, over bit-vectors, which needs
      // both of the options interpolation depends on
      Sort bv8 = s->make_sort(BV, 8);
      Term x = s->make_symbol("x", bv8);
      Term y = s->make_symbol("y", bv8);
      Term A = s->make_term(
          And,
          s->make_term(Equal, s->make_term(BVAdd, x, y), s->make_term(3, bv8)),
          s->make_term(Equal, y, s->make_term(1, bv8)));
      Term B = s->make_term(Equal, x, s->make_term(5, bv8));
      Term I;
      EXPECT_TRUE(s->get_interpolant(A, B, I).is_unsat()) << "round " << round;
      EXPECT_TRUE(I) << "round " << round;
    }
    s->reset();
  }
}

TEST(MsatInterpolants, InterpolatesAfterResetAssertions)
{
  SmtInterpolator s = MsatSolverFactory::create_interpolating_solver();
  // the BV query of InterpolatesAfterReset
  Sort bv8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bv8);
  Term y = s->make_symbol("y", bv8);
  Term A = s->make_term(
      And,
      s->make_term(Equal, s->make_term(BVAdd, x, y), s->make_term(3, bv8)),
      s->make_term(Equal, y, s->make_term(1, bv8)));
  Term B = s->make_term(Equal, x, s->make_term(5, bv8));
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
