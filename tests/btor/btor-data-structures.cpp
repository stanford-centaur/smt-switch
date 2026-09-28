/*********************                                                        */
/*! \file btor-data-structures.cpp
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

#include "boolector_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/boolector_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

TEST(BtorDataStructures, TermAndSortContainers)
{
  unsigned int NUM_TERMS = 20;

  // Create a LoggingSolver version
  SmtSolver s = BoolectorSolverFactory::create(true);
  s->set_opt("produce-models", "true");
  Sort bvsort8 = s->make_sort(BV, 8);

  UnorderedTermSet uts;
  UnorderedTermMap utm;
  TermVec v;
  v.reserve(NUM_TERMS);
  Term x;
  Term y;
  for (size_t i = 0; i < NUM_TERMS; ++i)
  {
    x = s->make_symbol("x" + to_string(i), bvsort8);
    y = s->make_symbol("y" + to_string(i), bvsort8);
    v.push_back(x);
    uts.insert(x);
    utm[x] = y;
  }

  Term trailing = v[0];
  for (size_t i = 1; i < NUM_TERMS; ++i)
  {
    s->assert_formula(s->make_term(
        Equal, v[i], s->make_term(BVAdd, trailing, s->make_term(1, bvsort8))));
    trailing = v[i];
  }

  Term zero = s->make_term(0, bvsort8);

  EXPECT_TRUE(zero->is_value());
  EXPECT_FALSE(v[0]->is_value());
  EXPECT_TRUE(v[0]->is_symbolic_const());

  Term v0_eq_0 = s->make_term(Equal, v[0], zero);
  s->assert_formula(v0_eq_0);

  // just assign all ys to x counterparts
  for (auto it = uts.begin(); it != uts.end(); ++it)
  {
    x = *it;
    y = utm.at(*it);
    s->assert_formula(s->make_term(Equal, x, y));
  }

  ASSERT_TRUE(s->check_sat().is_sat());

  EXPECT_TRUE(v[0]->is_symbolic_const());

  for (size_t i = 0; i < v.size(); ++i)
  {
    s->substitute(v[i], utm);
  }

  // x0 = 0 and each x_i = x_(i-1) + 1 force x_i = i; each y_i equals x_i
  for (size_t i = 0; i < NUM_TERMS; ++i)
  {
    EXPECT_EQ(s->get_value(v[i])->to_int(), i);
    EXPECT_EQ(s->get_value(utm.at(v[i]))->to_int(), i);
  }

  // create sets of sorts
  UnorderedSortSet sset;
  Sort s0, s1, s2, s3;
  s0 = s->make_sort(BV, 1);
  s1 = s->make_sort(BV, 4);
  s2 = s->make_sort(BOOL);
  s3 = s->make_sort(BV, 5);
  sset.insert(s0);
  sset.insert(s1);
  sset.insert(s2);
  sset.insert(s3);

  // boolector wold alias bool and BV{1}, but the LoggingSolver
  // wrapper will distinguish!
  // So, we expect 4 sorts
  EXPECT_EQ(sset.size(), 4);
}
