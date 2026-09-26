/*********************                                                        */
/*! \file msat-transfer.cpp
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

TEST(MsatTransfer, TransferBv)
{
  SmtSolver s = MsatSolverFactory::create(false);
  s->set_opt("produce-models", "true");
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term y = s->make_symbol("y", bvsort8);
  Term z = s->make_symbol("z", bvsort8);
  Term T = s->make_term(true);

  Term a = s->make_symbol("a", s->make_sort(INT));
  Term b = s->make_symbol("b", s->make_sort(INT));

  Term constraint = s->make_term(Equal, z, s->make_term(BVAdd, x, y));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, b));
  s->assert_formula(constraint);

  SmtSolver s2 = MsatSolverFactory::create(false);
  s2->set_opt("produce-models", "true");
  s2->set_opt("incremental", "true");

  TermTranslator tt(s2);

  Term constraint2 = tt.transfer_term(constraint);
  tt.transfer_term(T);
  // ensure it can handle transferring again (even though it already built the
  // node)
  constraint2 = tt.transfer_term(constraint);
  s2->assert_formula(constraint2);

  EXPECT_TRUE(s->check_sat().is_sat());
  EXPECT_TRUE(s2->check_sat().is_sat());
}

TEST(MsatTransfer, TransferInt)
{
  SmtSolver s = MsatSolverFactory::create(false);
  s->set_opt("produce-models", "true");
  Sort realsort = s->make_sort(REAL);
  Term x = s->make_symbol("x", realsort);
  Term y = s->make_symbol("y", realsort);
  Term one = s->make_term(1, realsort);
  Term two = s->make_term(2, realsort);
  Term half = s->make_term(Div, one, two);
  Term one_mod_two = s->make_term(Mod, one, two);
  Term T = s->make_term(true);

  Term a = s->make_symbol("a", s->make_sort(INT));

  Term constraint = s->make_term(Equal, half, s->make_term(Plus, x, y));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, one_mod_two));
  s->assert_formula(constraint);

  SmtSolver s2 = MsatSolverFactory::create(false);
  s2->set_opt("produce-models", "true");
  s2->set_opt("incremental", "true");

  TermTranslator tt(s2);

  Term constraint2 = tt.transfer_term(constraint);
  tt.transfer_term(T);
  // ensure it can handle transferring again (even though it already built the
  // node)
  constraint2 = tt.transfer_term(constraint);
  s2->assert_formula(constraint2);

  EXPECT_TRUE(s->check_sat().is_sat());
  EXPECT_TRUE(s2->check_sat().is_sat());
}
