/*!
 * \file msat-interpolator-options.cpp
 * \brief Tests which options a MathSAT interpolator refuses
 * \author Makai Mann
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <string>

#include "smt-switch/exceptions.h"
#include "smt-switch/interpolator.h"
#include "smt-switch/msat_factory.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"

using namespace smt;

TEST(MsatInterpolatorOptions, RefusesOnlyTheOptionsInterpolationNeeds)
{
  SmtInterpolator s = MsatSolverFactory::create_interpolator();
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
