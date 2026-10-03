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
