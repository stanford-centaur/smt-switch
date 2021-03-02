
#pragma once

#include "smt_defs.h"
#include <iostream>
#include "assert.h"
#include "smt.h"
#include <array>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include "assert.h"
#include "msat_factory.h"
#include "portfolio_solver.h"
#include "test-utils.h"
#include <string>
#include <unordered_map>
#include <utility>
#include "available_solvers.h"
#include <thread>
#include <cstdlib>
#include <unistd.h>
#include <mutex>
#include <condition_variable>

namespace smt {
  std::mutex m;
  std::condition_variable cv;
  bool someone_done = false;
  bool is_sat = false;

  bool do_solver(SmtSolver s, Term t) {
    TermTranslator to_s1(s);
    Term a = to_s1.transfer_term(t);
    s->assert_formula(a);
    is_sat = s->check_sat().is_sat();
    someone_done = true;
    cv.notify_all();
  }

  bool portfolio_solve(SmtSolver og, std::vector<SmtSolver> solvers, Term t) {

    for (auto s : solvers) {
      std::thread t1(do_solver, s, t);
      t1.detach();
    }

    // while !someone_done, wait
    // once someone is done, signal exit and return
    std::unique_lock<std::mutex> lk(m);
    cv.wait(lk, []{return someone_done;});

    // term translate then call solve on everyone. 
    return is_sat;
  }
} // namespace smt