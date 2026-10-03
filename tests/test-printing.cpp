/*********************                                                        */
/*! \file test-printing.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar, Áron Ricardo Perez-Lopez
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests that the solver's own executable answers what the printing
**        solver writes the same way the library did.
**
**/

#include <gtest/gtest.h>

#include <map>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "available_solvers.h"
#include "exec_utils.h"
#include "printing_solver.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

/** A solver's own executable, and the flags that have it read a printed
 *  session given as a file
 */
struct Executable
{
  string path;
  string flags;
};

// Each executable configure found, under the solver whose sessions it
// replays. A solver without one is left out.
const map<SolverEnum, Executable> executables = {
#ifdef BOOLECTOR_BINARY
  { BTOR, { BOOLECTOR_BINARY, "--incremental" } },
#endif
#ifdef BITWUZLA_BINARY
  { BZLA, { BITWUZLA_BINARY, "" } },
#endif
#ifdef CVC5_BINARY
  { CVC5, { CVC5_BINARY, "--incremental" } },
#endif
#ifdef MATHSAT_BINARY
  { MSAT, { MATHSAT_BINARY, "" } },
#endif
#ifdef YICES2_BINARY
  { YICES2, { YICES2_BINARY, "--incremental" } },
#endif
#ifdef Z3_BINARY
  { Z3, { Z3_BINARY, "-smt2" } },
#endif
};

/** The configurations with all the attributes whose solver has an
 *  executable
 */
vector<SolverConfiguration> replayable(
    const unordered_set<SolverAttribute> & attributes)
{
  vector<SolverConfiguration> result;
  for (SolverConfiguration sc : filter_solver_configurations(attributes))
  {
    // Yices2 terms print in Yices' own language rather than SMT-LIB, e.g.
    // (/= x y), so only the logging solver, which prints terms itself,
    // writes sessions the executable reads
    bool prints_smtlib = sc.solver_enum != YICES2 || sc.is_logging_solver;
    if (executables.count(sc.solver_enum) && prints_smtlib)
    {
      result.push_back(sc);
    }
  }
  return result;
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(PrintingTests);
class PrintingTests : public ::testing::Test,
                      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    // Boolector refuses push without it. Set before printing starts, since
    // not every executable takes it as an option; they get flags instead.
    SmtSolver wrapped = create_solver(GetParam());
    wrapped->set_opt("incremental", "true");
    s = create_printing_solver(wrapped, &os, PrintingStyleEnum::DEFAULT_STYLE);
    s->set_opt("produce-models", "true");
  }

  /** Declares b, which has to come after set-logic */
  void declare_b() { b = s->make_symbol("b", s->make_sort(BOOL)); }

  /** Replays what was printed, and checks that the executable answers with
   *  one of the expected lines for each command that has an answer
   */
  void expect_replay(const vector<unordered_set<string>> & expected)
  {
    const Executable & e = executables.at(GetParam().solver_enum);
    dump_and_run(e.path, strbuf, expected, e.flags);
  }

  stringbuf strbuf;
  ostream os{ &strbuf };
  SmtSolver s;
  Term b;
};

// MathSAT pads the parentheses of what it answers with spaces
const unordered_set<string> unsat_assumption_b = { "(b)", "( b )" };
const unordered_set<string> b_is_false = { "((b false))", "( (b false) )" };

TEST_P(PrintingTests, Solving)
{
  s->set_logic("QF_AUFBV");
  declare_b();
  Sort bvsort = s->make_sort(BV, 8);
  Sort funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
  Sort arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term arr = s->make_symbol("arr", arrsort);

  // Equal indices that read differently from the array, or that the
  // function maps apart, are unsatisfiable. In a pushed context, so that
  // popping it makes room for a satisfiable query.
  Term reads = s->make_term(
      Equal, s->make_term(Select, arr, x), s->make_term(Select, arr, y));
  Term apps =
      s->make_term(Equal, s->make_term(Apply, f, x), s->make_term(Apply, f, y));
  s->push(1);
  s->assert_formula(
      s->make_term(And,
                   s->make_term(Equal, x, y),
                   s->make_term(Not, s->make_term(And, reads, apps))));
  ASSERT_TRUE(s->check_sat().is_unsat());
  s->pop(1);
  s->assert_formula(s->make_term(Not, b));
  ASSERT_TRUE(s->check_sat().is_sat());
  s->get_value(b);

  expect_replay({ { "unsat" }, { "sat" }, b_is_false });
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(PrintingUnsatCoreTests);
class PrintingUnsatCoreTests : public PrintingTests
{
};

TEST_P(PrintingUnsatCoreTests, UnsatAssumptions)
{
  s->set_opt("produce-unsat-assumptions", "true");
  s->set_logic("QF_BV");
  declare_b();
  s->assert_formula(s->make_term(Not, b));
  ASSERT_TRUE(s->check_sat_assuming(TermVec{ b }).is_unsat());
  UnorderedTermSet assumptions;
  s->get_unsat_assumptions(assumptions);

  expect_replay({ { "unsat" }, unsat_assumption_b });
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(PrintingUninterpretedSortTests);
class PrintingUninterpretedSortTests : public PrintingTests
{
};

TEST_P(PrintingUninterpretedSortTests, DeclaresSorts)
{
  s->set_logic("QF_UFBV");
  Sort us = s->make_sort("S", 0);
  Sort bvsort = s->make_sort(BV, 8);
  Sort funsort = s->make_sort(FUNCTION, SortVec{ bvsort, us });
  Term x = s->make_symbol("x", bvsort);
  Term g = s->make_symbol("g", funsort);
  Term u = s->make_symbol("u", us);
  s->assert_formula(s->make_term(Equal, s->make_term(Apply, g, x), u));
  ASSERT_TRUE(s->check_sat().is_sat());

  expect_replay({ { "sat" } });
}

INSTANTIATE_TEST_SUITE_P(,
                         PrintingTests,
                         testing::ValuesIn(replayable({ THEORY_BV })),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(,
                         PrintingUnsatCoreTests,
                         testing::ValuesIn(replayable({ THEORY_BV,
                                                        UNSAT_CORE })),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(,
                         PrintingUninterpretedSortTests,
                         testing::ValuesIn(replayable({ THEORY_BV,
                                                        UNINTERP_SORT })),
                         ConfigName());

}  // namespace smt_tests
