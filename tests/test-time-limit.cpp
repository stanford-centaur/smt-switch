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

#include <chrono>
#include <cmath>
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
  }
  /** Asserts a pigeonhole problem too hard to finish inside the limit, and
   *  returns a free boolean usable as a check_sat_assuming assumption.
   */
  Term set_up_hard_problem(const SmtSolver & solver) const
  {
    solver->set_opt("incremental", "true");
    solver->set_opt("time-limit", std::to_string(time_limit));

    Term b = solver->make_symbol("b", solver->make_sort(BOOL));
    solver->assert_formula(b);

    // Bitwuzla ties a sort to the solver that made it, so each solver has to
    // build its own rather than share one from the fixture.
    Sort bvsort = solver->make_sort(BV, bv_width);
    size_t num_vars = (size_t)std::pow(2, bv_width) + 1;
    TermVec vars;
    vars.reserve(num_vars);
    for (size_t i = 0; i < num_vars; ++i)
    {
      vars.push_back(solver->make_symbol("x" + std::to_string(i), bvsort));
    }

    solver->push();
    for (size_t i = 0; i < num_vars - 1; ++i)
    {
      for (size_t j = i + 1; j < num_vars; ++j)
      {
        solver->assert_formula(solver->make_term(Distinct, vars[i], vars[j]));
      }
    }
    return b;
  }

  SmtSolver s;
  uint64_t bv_width = 6;
  int time_limit = 1;
};

TEST_P(TimeLimitTests, TestTimeLimit)
{
  set_up_hard_problem(s);

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

TEST_P(TimeLimitTests, TestTimeLimitAssuming)
{
  // Both entry points have to describe a timeout the same way. Yices2's
  // check_sat_assuming worked out whether the limit had fired and then threw
  // that away, answering a bare unknown where check_sat said why. Each check
  // gets its own solver: a context interrupted by the limit does not accept
  // another query.
  Term b = set_up_hard_problem(s);
  Result assuming = s->check_sat_assuming({ b });
  ASSERT_TRUE(assuming.is_unknown());

  SmtSolver plain_solver = create_solver(GetParam());
  plain_solver->set_opt("produce-models", "true");
  set_up_hard_problem(plain_solver);
  Result plain = plain_solver->check_sat();
  ASSERT_TRUE(plain.is_unknown());

  ASSERT_EQ(assuming.get_explanation(), plain.get_explanation());
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedTimeLimitTests,
    TimeLimitTests,
    testing::ValuesIn(filter_solver_configurations({ TIMELIMIT })));

}  // namespace smt_tests
