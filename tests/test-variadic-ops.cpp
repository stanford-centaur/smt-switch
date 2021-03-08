/*********************                                                        */
/*! \file test-variadic-ops.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for applying n-ary operators
**
**
**/

#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class VariadicOpsTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 8);
  }
  SmtSolver s;
  Sort boolsort, bvsort;
};

TEST_P(VariadicOpsTests, AND)
{
  size_t num_args = 20;
  TermVec args;
  args.reserve(num_args);

  for (size_t i = 0; i < num_args; ++i)
  {
    args.push_back(s->make_symbol("b" + std::to_string(i), boolsort));
  }

  Term reduce_and = s->make_term(And, args);
  s->assert_formula(reduce_and);
  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  Term term_true = s->make_term(true);

  for (const auto & a : args)
  {
    EXPECT_EQ(s->get_value(a), term_true);
  }
}

TEST_P(VariadicOpsTests, BVADD)
{
  size_t num_args = 20;
  TermVec args;
  args.reserve(num_args);

  size_t sum = 0;
  for (size_t i = 0; i < num_args; ++i)
  {
    args.push_back(s->make_symbol("x" + std::to_string(i), bvsort));
    s->assert_formula(
        s->make_term(Equal, args.back(), s->make_term(i, bvsort)));
    sum += i;
  }

  Term term_sum = s->make_term(BVAdd, args);
  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  ASSERT_EQ(s->get_value(term_sum)->to_int(), sum);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverVariadicOpsTests,
                         VariadicOpsTests,
                         testing::ValuesIn(available_solver_configurations()));

}  // namespace smt_tests
