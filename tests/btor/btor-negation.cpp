/*********************                                                        */
/*! \file btor-negation.cpp
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

#include <string>

#include "smt-switch/boolector_factory.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

using namespace smt;
using namespace std;

TEST(BtorNegation, LiteSolver)
{
  // Boolector doesn't have a NOT node
  // instead they just set the LSB of the id/pointer
  // to retrieve the real node, it needs btor_node_real_addr
  // this simple test is to ensure that smt-switch is handling this correctly

  // creating a solver WITHOUT smt-switch level logging of terms
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_logic("QF_ABV");
  s->set_opt("produce-models", "true");
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term five = s->make_term(5, bvsort8);
  Term ult5 = s->make_term(BVUlt, x, five);
  Term nult5 = s->make_term(Not, ult5);

  // Boolector turns everything into bv ops
  EXPECT_EQ(nult5->get_op(), BVNot);
  for (auto c : nult5)
  {
    EXPECT_EQ(c, ult5);
  }
  EXPECT_EQ(s->make_term(Not, nult5), ult5);
  EXPECT_EQ(s->make_term(Not, nult5)->get_op(), BVUlt);
}

TEST(BtorNegation, InversionFromSubstitution)
{
  // Substituting all ones for x leaves the xor of x and y as the negation
  // of y, and the xnor as y itself, which Boolector shows only by inverting
  // the node they simplify to.
  SmtSolver s = BoolectorSolverFactory::create(false);
  Sort bvsort4 = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bvsort4);
  Term y = s->make_symbol("y", bvsort4);
  Term bvxor = s->make_term(BVXor, x, y);
  Term bvxnor = s->make_term(BVXnor, x, y);
  s->assert_formula(s->make_term(Equal, x, s->make_term(0b1111, bvsort4)));
  ASSERT_TRUE(s->check_sat().is_sat());

  EXPECT_EQ(bvxor->get_op(), BVNot);
  TermVec children(bvxor->begin(), bvxor->end());
  ASSERT_EQ(children.size(), 1);
  EXPECT_EQ(children[0], y);
  EXPECT_NE(bvxnor->get_op(), BVNot);
}

TEST(BtorNegation, LoggingSolver)
{
  // creating a solver WITH smt-switch level logging of terms
  SmtSolver s = BoolectorSolverFactory::create(true);
  s->set_logic("QF_ABV");
  s->set_opt("produce-models", "true");
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term five = s->make_term(5, bvsort8);
  Term ult5 = s->make_term(BVUlt, x, five);
  Term nult5 = s->make_term(Not, ult5);

  EXPECT_EQ(nult5->get_op(), Not);
  for (auto c : nult5)
  {
    EXPECT_EQ(c, ult5);
  }

  // terms no longer rewritten on the fly
  EXPECT_NE(s->make_term(Not, nult5), ult5);
  EXPECT_EQ(s->make_term(Not, nult5)->get_op(), Not);
}
