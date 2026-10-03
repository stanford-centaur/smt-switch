/*********************                                                        */
/*! \file bzla-interpolants.cpp
** \verbatim
** Top contributors (to current version):
**   Po-Chun Chien
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

#include "bitwuzla_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/bitwuzla_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;

TEST(BzlaInterpolants, GetInterpolant)
{
  SmtInterpolator s = BitwuzlaSolverFactory::create_interpolating_solver();
  Sort bv8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bv8);
  Term y = s->make_symbol("y", bv8);
  Term z = s->make_symbol("z", bv8);

  EXPECT_THROW(s->assert_formula(s->make_term(Equal, x, s->make_term(0, bv8))),
               IncorrectUsageException);

  Term A =
      s->make_term(And, s->make_term(BVUlt, x, y), s->make_term(BVUlt, y, z));
  Term B = s->make_term(BVUgt, x, z);
  Term I;
  Result r = s->get_interpolant(A, B, I);

  EXPECT_TRUE(r.is_unsat());

  s->reset_assertions();

  // try getting another interpolant with different A and B
  A = s->make_term(And, s->make_term(BVUgt, x, y), s->make_term(BVUgt, y, z));
  B = s->make_term(BVUlt, x, z);
  r = s->get_interpolant(A, B, I);

  EXPECT_TRUE(r.is_unsat());

  // try getting an interpolant with A itself being unsat
  Term unsat_term =
      s->make_term(And, s->make_term(BVUgt, z, y), s->make_term(BVUgt, y, z));
  r = s->get_interpolant(unsat_term, B, I);

  EXPECT_TRUE(r.is_unsat());

  // try getting an interpolant with B itself being unsat
  r = s->get_interpolant(A, unsat_term, I);

  EXPECT_TRUE(r.is_unsat());

  // now try a satisfiable formula
  r = s->get_interpolant(A, s->make_term(BVUgt, x, z), I);
  EXPECT_TRUE(r.is_sat());
}

TEST(BzlaInterpolants, ResetAfterInterpolant)
{
  SmtInterpolator s = BitwuzlaSolverFactory::create_interpolating_solver();
  {
    // after this block only the solver holds the query's terms
    Sort bv8 = s->make_sort(BV, 8);
    Term x = s->make_symbol("x", bv8);
    Term I;
    ASSERT_TRUE(s->get_interpolant(s->make_term(Equal, x, s->make_term(1, bv8)),
                                   s->make_term(Equal, x, s->make_term(2, bv8)),
                                   I)
                    .is_unsat());
  }
  s->reset();

  // x is gone, so its name can be declared again
  EXPECT_NO_THROW(s->make_symbol("x", s->make_sort(BOOL)));
}
