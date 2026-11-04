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
** \brief Tests for creating MathSAT solvers.
**
**
**/
#include <gtest/gtest.h>
#include <mathsat.h>

#include <memory>
#include <string>

#include "interpolating_solver.h"
#include "msat_solver.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"

using namespace smt;

namespace {

TEST(MsatConstructors, GetMsatEnvCreatesTheEnv)
{
  std::shared_ptr<MsatSolver> s = std::make_shared<MsatSolver>();
  std::shared_ptr<msat_env> env = s->get_msat_env();
  ASSERT_FALSE(MSAT_ERROR_ENV(*env));
  // the solver goes on using the env it handed out
  s->make_symbol("x", s->make_sort(BOOL));
  EXPECT_EQ(s->get_msat_env(), env);
}

TEST(MsatConstructors, InterpolatingKeepsBitBlastPreference)
{
  // x + y = 3 and y = 1 against x = 5, over bit-vectors: MathSAT's default
  // eager BV solver cannot produce the proofs interpolation needs, whatever
  // bit-blasting mode the caller prefers
  SmtInterpolator s = std::make_shared<MsatInterpolatingSolver>();
  s->set_opt("theory.bv.bit_blast_mode", "1");
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

}  // namespace
