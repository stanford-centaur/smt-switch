#pragma once

#include "smt.h"
#include <thread>
#include <mutex>
#include <condition_variable>

namespace smt {
  std::mutex m;
  std::condition_variable cv;
  bool a_solver_is_done = false;
  bool is_sat = false;

  bool do_solver(SmtSolver s, Term t) {
    TermTranslator to_s1(s);
    Term a = to_s1.transfer_term(t);
    s->assert_formula(a);
    is_sat = s->check_sat().is_sat();
    std::lock_guard<std::mutex> lk(m);
    a_solver_is_done = true;
    cv.notify_all();
  }

  bool portfolio_solve(SmtSolver og, std::vector<SmtSolver> solvers, Term t) {

    for (auto s : solvers) {
      std::thread t1(do_solver, s, t);
      t1.detach();
    }

    std::unique_lock<std::mutex> lk(m);
    cv.wait(lk, []{return a_solver_is_done;});

    return is_sat;
  }
} // namespace smt