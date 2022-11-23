/*********************                                                        */
/*! \file test-time-limit.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for time limit option.
**
**
**/

#include <math.h>

#include <chrono>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(TimeLimitTests);
class TimeLimitTests : public ::testing::Test,
                       public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    bvsort = s->make_sort(BV, 6);
  }
  SmtSolver s;
  Sort bvsort;
  int time_limit = 1;
};

TEST_P(TimeLimitTests, TestTimeLimit)
{
  s->set_opt("incremental", "true");
  s->set_opt("time-limit", std::to_string(time_limit));

  // create a difficult pigeonhole problem
  size_t width = bvsort->get_width();

  s->assert_formula(s->make_symbol("b", s->make_sort(BOOL)));

  size_t num_vars = (size_t)pow(2, width) + 1;
  TermVec vars;
  vars.reserve(num_vars);
  for (size_t i = 0; i < num_vars; ++i)
  {
    vars.push_back(s->make_symbol("x" + std::to_string(i), bvsort));
  }

  s->push();
  for (size_t i = 0; i < num_vars - 1; ++i)
  {
    for (size_t j = i + 1; j < num_vars; ++j)
    {
      s->assert_formula(s->make_term(Distinct, vars[i], vars[j]));
    }
  }
  auto start = std::chrono::high_resolution_clock::now();
  Result r = s->check_sat();
  auto stop = std::chrono::high_resolution_clock::now();
  auto duration =
      std::chrono::duration_cast<std::chrono::seconds>(stop - start);
  ASSERT_TRUE(r.is_unknown());
  ASSERT_TRUE((duration.count() - time_limit) < 1);
  s->pop();
  r = s->check_sat();
  ASSERT_TRUE(r.is_sat());
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedTimeLimitTests,
    TimeLimitTests,
    testing::ValuesIn(filter_solver_configurations({ TIMELIMIT })));

}  // namespace smt_tests
