/*********************                                                        */
/*! \file msat-constructors.cpp
** \verbatim
** Top contributors (to current version):
**   Áron Ricardo Perez-Lopez
** This file is part of the smt-switch project.
** Copyright (c) 2026 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for creating MathSAT solvers from a caller's configuration.
**
**
**/
#include <gtest/gtest.h>

#include <memory>

#include "mathsat.h"
#include "msat_solver.h"
#include "smt.h"

using namespace smt;

namespace smt_tests {

// x < y < z and x > z have the interpolant x < z (or an equivalent)
static void expect_interpolant(const SmtSolver & s)
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

// x + y = 3 and y = 1 against x = 5, over bit-vectors: MathSAT's default
// eager BV solver cannot produce the proofs interpolation needs
static void expect_bv_interpolant(const SmtSolver & s)
{
  Sort bvsort = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term A = s->make_term(
      And,
      s->make_term(Equal, s->make_term(BVAdd, x, y), s->make_term(3, bvsort)),
      s->make_term(Equal, y, s->make_term(1, bvsort)));
  Term B = s->make_term(Equal, x, s->make_term(5, bvsort));
  Term I;
  EXPECT_TRUE(s->get_interpolant(A, B, I).is_unsat());
  EXPECT_TRUE(I);
}

TEST(MsatConstructors, ConfigAcceptsOptionsUntilFirstUse)
{
  SmtSolver s = std::make_shared<MsatSolver>(msat_create_config());
  s->set_opt("produce-models", "true");
  Sort bvsort = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bvsort);
  Term three = s->make_term(3, bvsort);
  s->assert_formula(s->make_term(Equal, x, three));
  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_EQ(s->get_value(x), three);
}

TEST(MsatConstructors, GetMsatEnvCreatesTheEnv)
{
  std::shared_ptr<MsatSolver> s = std::make_shared<MsatSolver>();
  msat_env env = s->get_msat_env();
  ASSERT_FALSE(MSAT_ERROR_ENV(env));
  // the solver goes on using the env it handed out
  s->make_symbol("x", s->make_sort(BOOL));
  EXPECT_EQ(s->get_msat_env().repr, env.repr);
}

TEST(MsatConstructors, InterpolatingFromConfig)
{
  msat_config cfg = msat_create_config();
  msat_set_option(cfg, "dpll.ghost_filtering", "true");
  expect_interpolant(std::make_shared<MsatInterpolatingSolver>(cfg));
}

TEST(MsatConstructors, InterpolatingDefaultConfigOnBitVectors)
{
  expect_bv_interpolant(std::make_shared<MsatInterpolatingSolver>());
}

TEST(MsatConstructors, InterpolatingForcesRequiredOptions)
{
  // the two options interpolation cannot do without are overridden
  msat_config cfg = msat_create_config();
  msat_set_option(cfg, "interpolation", "false");
  msat_set_option(cfg, "theory.bv.eager", "true");
  msat_set_option(cfg, "theory.bv.bit_blast_mode", "1");
  expect_bv_interpolant(std::make_shared<MsatInterpolatingSolver>(cfg));
}

}  // namespace smt_tests
