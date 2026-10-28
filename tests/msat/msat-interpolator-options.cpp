/*********************                                                        */
/*! \file msat-interpolator-options.cpp
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

#include "exceptions.h"
#include "interpolating_solver.h"
#include "msat_factory.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "sort.h"

using namespace smt;

TEST(MsatInterpolatorOptions, RefusesOnlyTheOptionsInterpolationNeeds)
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
