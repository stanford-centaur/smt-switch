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

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"

TEST(MsatConstructors, DeprecatedConfigAndEnv)
{
  msat_config cfg = msat_create_config();
  msat_env env = msat_create_env(cfg);
  std::shared_ptr<MsatSolver> s = std::make_shared<MsatSolver>(cfg, env);
  EXPECT_EQ(s->get_msat_env().repr, env.repr);
  Term p = s->make_symbol("p", s->make_sort(BOOL));
  s->assert_formula(p);
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST(MsatConstructors, DeprecatedInterpolatingOwnsBoth)
{
  // as pono calls it: the solver owns cfg and env, so neither is destroyed
  // here, and the solver works from an env it creates itself
  msat_config cfg = msat_create_config();
  msat_env env = msat_create_env(cfg);
  expect_interpolant(std::make_shared<MsatInterpolatingSolver>(cfg, env));
}

#pragma GCC diagnostic pop

}  // namespace smt_tests
