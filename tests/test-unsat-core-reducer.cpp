/*********************                                                        */
/*! \file test-unsat-assumption-reducer.cpp
** \verbatim
** Top contributors (to current version):
**   Ahmed Irfan, Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for unsat-assumption-based reducer.
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnsatCoreReducerTests);
class UnsatCoreReducerTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("incremental", "true");
    boolsort = s->make_sort(BOOL);
    bvsort32 = s->make_sort(BV, 32);

    r = create_solver(GetParam());
  }
  SmtSolver s;
  Sort boolsort, bvsort32;
  SmtSolver r;
};

TEST_P(UnsatCoreReducerTests, UnsatCoreReducer)
{
  UnsatCoreReducer uscr(r);

  Term a = s->make_symbol("a", boolsort);
  Term b = s->make_symbol("b", boolsort);
  Term formula = s->make_term(And, a, b);
  TermVec assump({ s->make_term(Not, a), s->make_term(Not, b) });
  TermVec red, rem;

  uscr.reduce_assump_unsatcore(formula, assump, red, &rem);
  EXPECT_TRUE(red.size() == 1);
  EXPECT_TRUE(rem.size() == 1);
  EXPECT_TRUE(rem[0] != red[0]);
}

TEST_P(UnsatCoreReducerTests, UnsatCoreReducerSingle)
{
  UnsatCoreReducer uscr(r);

  Term a = s->make_symbol("a", bvsort32);
  Term b = s->make_symbol("b", bvsort32);

  Op ext = Op(Extract, 15, 0);
  Term a0 = s->make_term(ext, a);
  Term b0 = s->make_term(ext, b);

  Term ab = s->make_term(BVAnd, a, b);
  Term t1 = s->make_term(BVUge, a0, b0);
  Term t2 = s->make_term(BVUge, ab, a);
  Term t3 = s->make_term(BVUge, ab, b);

  Term formula = s->make_term(Distinct, a, b);
  TermVec assumps({ t1, t2, t3 });
  TermVec red, rem;

  uscr.reduce_assump_unsatcore(formula, assumps, red, &rem, 1);

  s->assert_formula(formula);
  Result rbefore = s->check_sat();
  EXPECT_TRUE(rbefore.is_sat());
  for (const auto & tt : assumps)
  {
    s->assert_formula(tt);
  }
  Result rafter = s->check_sat();
  EXPECT_TRUE(rafter.is_unsat());
}

TEST_P(UnsatCoreReducerTests, UnsatCoreReducerLinear)
{
  UnsatCoreReducer uscr(r);

  Term a = s->make_symbol("a", boolsort);
  Term b = s->make_symbol("b", boolsort);
  Term formula = s->make_term(And, a, b);
  TermVec assump({ s->make_term(Not, a), s->make_term(Not, b) });
  TermVec red, rem;

  uscr.linear_reduce_assump_unsatcore(formula, assump, red, &rem);
  EXPECT_EQ(red.size() , 1);
  EXPECT_EQ(rem.size() , 1);
  EXPECT_NE(rem[0] , red[0]);
}

// The unsat cores reducer module requires the
// underlying solver to support both unsat cores
// and term translation.
INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverUnsatCoreReducerTests,
    UnsatCoreReducerTests,
    testing::ValuesIn(filter_non_generic_solver_configurations(
        { UNSAT_CORE, FULL_TRANSFER })));

}  // namespace smt_tests
