/*!
 * \file yices2-exceptions.cpp
 * \brief The exceptions Yices2 throws for failed calls and refused operators
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Yices keeps the code of its last error until it is cleared, so a failed
 * call that is reported without clearing it would be reported again by the
 * next call that checks for one.
 */
#include <gtest/gtest.h>

#include <chrono>
#include <cstddef>
#include <future>
#include <string>
#include <thread>

#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/yices2_factory.h"

using namespace smt;

TEST(Yices2Exceptions, LaterCallsDoNotReportAnEarlierError)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  EXPECT_THROW(s->make_sort(BV, 0), IncorrectUsageException);
  EXPECT_NO_THROW(s->make_sort(BV, 4));

  SmtSolver fresh = Yices2SolverFactory::create(false);
  EXPECT_NO_THROW(fresh->make_sort(BV, 4));
}

TEST(Yices2Exceptions, RefusedPushLeavesNoError)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  s->set_opt("incremental", "false");
  EXPECT_THROW(s->push(), NotImplementedException);
  EXPECT_EQ(s->get_context_level(), 0u);
  EXPECT_NO_THROW(s->make_sort(BV, 4));
}

TEST(Yices2Exceptions, MissingOperatorsAreNotImplemented)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort bvsort = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);

  Term p = s->make_param("p", bvsort);
  Term body = s->make_term(Equal, p, y);

  EXPECT_THROW(s->make_term(Apply_Tester, x, y), NotImplementedException);
  EXPECT_THROW(s->make_term(Forall, p, body), NotImplementedException);
}

TEST(Yices2Exceptions, MisappliedOperatorsAreIncorrectUsage)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort bvsort = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);

  EXPECT_THROW(s->make_term(Op(Not, 3), x), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Op(Extract, 3, 0), x, y), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Concat, x), IncorrectUsageException);
}

// checks s, first telling started that its thread is running
static Result check_once_started(SmtSolver s, std::promise<void> * started)
{
  started->set_value();
  return s->check_sat();
}

TEST(Yices2Exceptions, OneTimeLimitedCheckAtATime)
{
  // a pigeonhole problem too hard to finish inside its limit
  SmtSolver hard = Yices2SolverFactory::create(false);
  hard->set_opt("time-limit", "0.1");
  Sort bvsort = hard->make_sort(BV, 6);
  TermVec vars;
  for (size_t i = 0; i < 65; ++i)
  {
    vars.push_back(hard->make_symbol("x" + std::to_string(i), bvsort));
  }
  for (size_t i = 0; i + 1 < vars.size(); ++i)
  {
    for (size_t j = i + 1; j < vars.size(); ++j)
    {
      hard->assert_formula(hard->make_term(Distinct, vars[i], vars[j]));
    }
  }

  SmtSolver other = Yices2SolverFactory::create(false);
  other->set_opt("time-limit", "0.1");

  std::promise<void> started;
  std::future<Result> running =
      std::async(std::launch::async, check_once_started, hard, &started);
  // Waiting for the thread, however slow it is to be scheduled, leaves only
  // the few calls between its signal and its claim of the timer to sleep
  // through.
  started.get_future().wait();
  std::this_thread::sleep_for(std::chrono::milliseconds(10));
  // the running check holds the process's one time-limit timer
  EXPECT_THROW(other->check_sat(), NotImplementedException);
  // the refused check left the running one's limit in place
  EXPECT_TRUE(running.get().is_unknown());
}
