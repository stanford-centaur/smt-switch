/*!
 * \file yices2-time-limit.cpp
 * \brief Tests that Yices2 time limits leave the program's own SIGALRM alone
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Yices2 time limits run on the process's one SIGALRM timer, which the
 * program may be using as well.
 */
#include <gtest/gtest.h>
#include <signal.h>
#include <sys/time.h>

#include <cstddef>
#include <string>

#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/yices2_factory.h"

using namespace smt;

namespace {

volatile sig_atomic_t program_alarms = 0;

void count_program_alarm(int /* signum */)
{
  program_alarms = program_alarms + 1;
}

// asserts a pigeonhole problem too hard to finish inside a short limit
void assert_pigeonhole(const SmtSolver & s)
{
  Sort bvsort = s->make_sort(BV, 6);
  TermVec vars;
  for (size_t i = 0; i < 65; ++i)
  {
    vars.push_back(s->make_symbol("x" + std::to_string(i), bvsort));
  }
  for (size_t i = 0; i + 1 < vars.size(); ++i)
  {
    for (size_t j = i + 1; j < vars.size(); ++j)
    {
      s->assert_formula(s->make_term(Distinct, vars[i], vars[j]));
    }
  }
}

class Yices2TimeLimit : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    program_alarms = 0;
    struct sigaction counting{};
    counting.sa_handler = count_program_alarm;
    sigemptyset(&counting.sa_mask);
    sigaction(SIGALRM, &counting, &previous_action);
  }

  void TearDown() override
  {
    itimerval disarm{};
    setitimer(ITIMER_REAL, &disarm, nullptr);
    sigaction(SIGALRM, &previous_action, nullptr);
  }

  // the handler SIGALRM runs now
  static void (*current_handler())(int)
  {
    struct sigaction current{};
    sigaction(SIGALRM, nullptr, &current);
    return current.sa_handler;
  }

  struct sigaction previous_action{};
};

TEST_F(Yices2TimeLimit, KeepsTheProgramsHandler)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  s->set_opt("time-limit", "10");
  Term x = s->make_symbol("x", s->make_sort(BOOL));
  s->assert_formula(x);

  EXPECT_TRUE(s->check_sat().is_sat());
  EXPECT_EQ(current_handler(), count_program_alarm);
  raise(SIGALRM);
  EXPECT_EQ(program_alarms, 1);
}

TEST_F(Yices2TimeLimit, KeepsTheProgramsHandlerAfterTheLimitFires)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  s->set_opt("time-limit", "0.1");
  assert_pigeonhole(s);

  EXPECT_TRUE(s->check_sat().is_unknown());
  EXPECT_EQ(current_handler(), count_program_alarm);
  // the limit's own alarm went to the solver's handler
  EXPECT_EQ(program_alarms, 0);
}

TEST_F(Yices2TimeLimit, RefusesALimitWhileTheProgramsTimerIsArmed)
{
  itimerval program_timer{};
  program_timer.it_value.tv_sec = 60;
  setitimer(ITIMER_REAL, &program_timer, nullptr);

  SmtSolver s = Yices2SolverFactory::create(false);
  s->set_opt("time-limit", "10");
  EXPECT_THROW(s->check_sat(), NotImplementedException);

  itimerval remaining{};
  getitimer(ITIMER_REAL, &remaining);
  EXPECT_GT(remaining.it_value.tv_sec, 0);
  EXPECT_EQ(current_handler(), count_program_alarm);

  // the refusal gave the timer back
  itimerval disarm{};
  setitimer(ITIMER_REAL, &disarm, nullptr);
  SmtSolver other = Yices2SolverFactory::create(false);
  other->set_opt("time-limit", "10");
  EXPECT_TRUE(other->check_sat().is_sat());
}

}  // namespace
