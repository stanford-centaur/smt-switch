/*********************                                                        */
/*! \file yices2-neg-numbers.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
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

#include "smt.h"
#include "yices2_factory.h"
// after a full installation
// #include "smt-switch/yices2_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;

TEST(Yices2NegNumbers, NegativeValues)
{
  SmtSolver s = Yices2SolverFactory::create(true);

  // BitVector cases
  Sort bvsort8 = s->make_sort(BV, 8);

  Term four = s->make_term(4, bvsort8);
  Term neg_four = s->make_term(-4, bvsort8);

  EXPECT_EQ(neg_four, s->make_term("-4", bvsort8));

  EXPECT_THROW(s->make_term("-129", bvsort8), IncorrectUsageException);

  s->push();
  s->assert_formula(
      s->make_term(Not,
                   s->make_term(Equal,
                                s->make_term(BVAdd, four, neg_four),
                                s->make_term(0, bvsort8))));
  Result r = s->check_sat();
  EXPECT_TRUE(r.is_unsat());
  s->pop();

  r = s->check_sat();
  EXPECT_TRUE(r.is_sat());

  // Integer cases
  Sort intsort = s->make_sort(INT);
  Term five = s->make_term(5, intsort);
  Term neg_five = s->make_term(-5, intsort);

  EXPECT_EQ(neg_five, s->make_term("-5", intsort));

  s->push();
  s->assert_formula(
      s->make_term(Not,
                   s->make_term(Equal,
                                s->make_term(Plus, five, neg_five),
                                s->make_term("0", intsort))));
  r = s->check_sat();
  EXPECT_TRUE(r.is_unsat());
  s->pop();
}
