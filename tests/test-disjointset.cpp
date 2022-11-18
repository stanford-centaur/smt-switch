/*********************                                                        */
/*! \file test-disjointset.cpp
** \verbatim
** Top contributors (to current version):
**   Ahmed Irfan, Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for disjoint-set.
**
**
**/

#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"
#include "utils.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class DisjointSetTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    bvsort = s->make_sort(BV, 8);
    x = s->make_symbol("x", bvsort);
    y = s->make_symbol("y", bvsort);
    z = s->make_symbol("z", bvsort);
    w = s->make_symbol("w", bvsort);
  }
  SmtSolver s;
  Sort bvsort;
  Term x, y, z, w;
};

static bool disjoint_set_rank(const Term & t1, const Term & t2)
{
  if (!t1->is_value() && !t2->is_value())
  {
    return t1 < t2;
  }
  return !t1->is_value();
}

TEST_P(DisjointSetTests, TestDisjointSet)
{
  Term t1, t2, t3, t4;
  DisjointSet ds(disjoint_set_rank);

  ds.add(z, y);
  t1 = ds.find(y);
  t2 = ds.find(z);
  EXPECT_TRUE(t1 == t2);

  ds.add(x, y);
  t3 = ds.find(x);
  EXPECT_TRUE(t1 == t3);

  ds.add(w, z);
  t4 = ds.find(w);
  EXPECT_TRUE(t1 == t4);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverDisjointSetTests,
                         DisjointSetTests,
                         testing::ValuesIn(available_solver_configurations()));

}  // namespace smt_tests
