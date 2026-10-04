/*********************                                                        */
/*! \file portfolio_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2021 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Implementation of a portfolio solving function that takes a vector
**        of solvers and a term, and returns check_sat from the first solver
**        that finishes.
**/

#include "portfolio_solver.h"

#include <pthread.h>
#include <sys/resource.h>
#include <unistd.h>

#include <algorithm>
#include <cstddef>
#include <cstring>
#include <functional>
#include <memory>
#include <mutex>
#include <string>
#include <utility>

#include "exceptions.h"
#include "smt_defs.h"
#include "sort.h"
#include "term_translator.h"

namespace {

// The stack each solver thread gets: the larger of 8 MB, what a main thread
// usually has, and the stack limit. std::thread leaves it to the platform,
// and macOS gives a thread only 512 KB, which a solver that walks a deep term
// recursively runs out of. A thread's stack is not bound by the limit.
std::size_t solver_stack_size()
{
  std::size_t size = 8 * 1024 * 1024;
  rlimit limit;
  if (getrlimit(RLIMIT_STACK, &limit) == 0 && limit.rlim_cur != RLIM_INFINITY)
  {
    size = std::max(size, static_cast<std::size_t>(limit.rlim_cur));
  }
  // macOS rejects a size that is not a whole number of pages.
  const auto page = static_cast<std::size_t>(sysconf(_SC_PAGESIZE));
  return (size + page - 1) / page * page;
}

void * run_job(void * arg)
{
  std::unique_ptr<std::function<void()>> job(
      static_cast<std::function<void()> *>(arg));
  (*job)();
  return nullptr;
}

// Throws if a pthread call reports an error.
void check(int error, const std::string & what)
{
  if (error != 0)
  {
    throw SmtException(what + ": " + std::strerror(error));
  }
}

// Runs job on a detached thread with solver_stack_size() of stack.
void start_detached(std::function<void()> job)
{
  pthread_attr_t attr;
  check(pthread_attr_init(&attr), "Could not set up a solver thread");
  // Destroys the attributes however this function is left.
  std::unique_ptr<pthread_attr_t, int (*)(pthread_attr_t *)> attr_guard(
      &attr, pthread_attr_destroy);
  check(pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED),
        "Could not make a solver thread detached");
  const std::size_t stack_size = solver_stack_size();
  check(pthread_attr_setstacksize(&attr, stack_size),
        "Could not give a solver thread a stack of "
            + std::to_string(stack_size) + " bytes");

  auto owned = std::make_unique<std::function<void()>>(std::move(job));
  pthread_t thread;
  check(pthread_create(&thread, &attr, run_job, owned.get()),
        "Could not start a solver thread");
  // The thread owns it now, and run_job frees it.
  owned.release();
}

}  // namespace

namespace smt {

PortfolioSolver::PortfolioSolver(std::vector<SmtSolver> slvrs, Term trm)
    : solvers(slvrs), portfolio_term(trm)
{
}

/** Translate the term t to the solver s, and check_sat.
 *  @param s The solver to translate the term t to.
 *  @param t The term being translated to solver s.
 */
void PortfolioSolver::run_solver(SmtSolver s)
{
  TermTranslator to_s(s);
  Term a = to_s.transfer_term(portfolio_term, BOOL);
  s->assert_formula(a);
  result = s->check_sat();
  std::lock_guard<std::mutex> lk(m);
  a_solver_is_done = true;

  cv.notify_all();
}

/** Launch many solvers and return whether the term is satisfiable when one of
 *  them has finished.
 *  @param solvers The solvers to run.
 *  @param t The term to be checked.
 */
Result PortfolioSolver::portfolio_solve()
{
  // We must maintain a vector of pthreads in order to stop the threads that are
  // still running once one of the solvers finish because pthreads is assumed to
  // be the underlying implementation.
  for (auto s : solvers)
  {
    // Detached, because we are not interested in waiting for all of them to
    // finish.
    start_detached([this, s] { run_solver(s); });
  }

  // Wait until a solver is done to cancel the threads that are still running.
  std::unique_lock<std::mutex> lk(m);
  while (!a_solver_is_done) cv.wait(lk);

  return result;
}

}  // namespace smt
