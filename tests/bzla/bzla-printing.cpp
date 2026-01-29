#include <gtest/gtest.h>

#include <cassert>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "bitwuzla_factory.h"
#include "printing_solver.h"
#include "smt.h"
#include "test-utils.h"

using namespace smt;

namespace smt_tests {

class BitwuzlaPrintingTest : public testing::Test
{
 protected:
  void SetUp() override { os = new std::ostream(&strbuf); }
  void TearDown() override { delete os; }
  void check_result(
      std::vector<std::unordered_set<std::string>> expected_results,
      std::string extra_opts = "")
  {
    dump_and_run(BZLA, strbuf, expected_results, extra_opts);
  }
  std::stringbuf strbuf;
  std::ostream * os;
};

TEST_F(BitwuzlaPrintingTest, Solving)
{
  SmtSolver solver =
      create_printing_solver(BitwuzlaSolverFactory::create(false),
                             os,
                             PrintingStyleEnum::DEFAULT_STYLE);
  solver->set_logic("QF_AUFBV");
  solver->set_opt("produce-models", "true");
  solver->set_opt("produce-unsat-assumptions", "true");
  Sort us = solver->make_sort("S", 0);
  Sort bvsort32 = solver->make_sort(BV, 32);
  Sort fun_sort = solver->make_sort(FUNCTION, SortVec{ bvsort32, us });
  Sort array32_32 = solver->make_sort(ARRAY, bvsort32, bvsort32);
  Term x = solver->make_symbol("x", bvsort32);
  Term y = solver->make_symbol("y", bvsort32);
  Term arr = solver->make_symbol("arr", array32_32);
  Term fun = solver->make_symbol("f", fun_sort);

  Term S0 = solver->make_symbol("s", us);

  Term ind1 = solver->make_symbol("ind1", solver->make_sort(BOOL));
  Term fx = solver->make_term(Apply, fun, x);
  Term id = solver->make_term(Equal, fx, fx);
  Term neq = solver->make_term(Not, solver->make_term(Equal, S0, S0));
  solver->push(1);
  solver->assert_formula(ind1);
  solver->assert_formula(id);
  solver->assert_formula(solver->make_term(Equal, ind1, neq));
  solver->assert_formula(solver->make_term(
      Not,
      solver->make_term(Implies,
                        solver->make_term(Equal, x, y),
                        solver->make_term(Equal,
                                          solver->make_term(Select, arr, x),
                                          solver->make_term(Select, arr, y)))));
  Result r = solver->check_sat_assuming(TermVec{ ind1 });
  assert(r.is_unsat());
  UnorderedTermSet usc;
  solver->get_unsat_assumptions(usc);
  solver->pop(1);
  solver->check_sat();
  solver->get_value(x);
  check_result({
      { "unsat" },
      { "(ind1)" },
      { "sat" },
      { "((x #b00000000000000000000000000000000))",
        "((x #b11111111111111111111111111111111))" },
  });
}

}  // namespace smt_tests
