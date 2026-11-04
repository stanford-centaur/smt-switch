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

#include <exception>
#include <memory>
#include <optional>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "available_solvers.h"
#include "exceptions.h"
#include "exec_utils.h"
#include "ops.h"
#include "printing_solver.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

/** The flags that have a solver's executable read a printed session given
 *  as a file
 */
string replay_flags(SolverEnum se)
{
  switch (se)
  {
    case BTOR: return "--incremental";
    case BZLA: return "";
    case CVC5: return "--incremental";
    case MSAT: return "";
    case YICES2: return "--incremental";
    case Z3: return "-smt2";
    case GENERIC_SOLVER:
    case BZLA_INTERPOLATOR:
    case CVC5_INTERPOLATOR:
    case MSAT_INTERPOLATOR:
    case YICES2_INTERPOLATOR: break;
  }
  throw NotImplementedException("No executable for " + to_string(se));
}

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
    if (solver_binary(sc.solver_enum) && prints_smtlib)
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
    SmtSolver wrapped = create_solver(GetParam());
    // Boolector refuses push without this. Set before printing starts, since
    // not every executable accepts it as an option; they get flags instead.
    wrapped->set_opt("incremental", "true");
    s = create_printing_solver(wrapped, &os);
    s->set_opt("produce-models", "true");
  }

  /** Replays what was printed, and checks that the executable answers with
   *  one of the expected lines for each command that has an answer
   */
  void expect_replay(const vector<unordered_set<string>> & expected)
  {
    SolverEnum se = GetParam().solver_enum;
    dump_and_run(solver_binary(se).value(), strbuf, expected, replay_flags(se));
  }

  stringbuf strbuf;
  ostream os{ &strbuf };
  SmtSolver s;
};

TEST_P(PrintingTests, RefusedSetLogicIsNotPrinted)
{
  bool accepted = true;
  try
  {
    s->set_logic("NOT_A_LOGIC");
  }
  catch (std::exception &)
  {
    accepted = false;
  }
  // printed exactly when the wrapped solver accepted it
  EXPECT_EQ(strbuf.str().find("NOT_A_LOGIC") != string::npos, accepted);
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(PrintingBitVectorTests);
class PrintingBitVectorTests : public PrintingTests
{
 protected:
  void SetUp() override
  {
    PrintingTests::SetUp();
    make_symbols();
  }

  void make_symbols()
  {
    s->set_logic("QF_AUFBV");
    bvsort = s->make_sort(BV, 8);
    b = s->make_symbol("b", s->make_sort(BOOL));
    x = s->make_symbol("x", bvsort);
    y = s->make_symbol("y", bvsort);
  }

  Sort bvsort;
  Term b, x, y;
};

TEST_P(PrintingBitVectorTests, Solving)
{
  Sort funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
  Sort arrsort = s->make_sort(ARRAY, bvsort, bvsort);
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

  // MathSAT pads the parentheses of what it answers with spaces
  expect_replay({ { "unsat" }, { "sat" }, { "((b false))", "( (b false) )" } });
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(PrintingUninterpretedSortTests);
class PrintingUninterpretedSortTests : public PrintingBitVectorTests
{
};

TEST_P(PrintingUninterpretedSortTests, DeclaresSorts)
{
  Sort us = s->make_sort("S", 0);
  Sort funsort = s->make_sort(FUNCTION, SortVec{ bvsort, us });
  Term g = s->make_symbol("g", funsort);
  Term u = s->make_symbol("u", us);
  s->assert_formula(s->make_term(Equal, s->make_term(Apply, g, x), u));
  ASSERT_TRUE(s->check_sat().is_sat());

  expect_replay({ { "sat" } });
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(PrintingUnsatCoreTests);
class PrintingUnsatCoreTests : public PrintingBitVectorTests
{
 protected:
  void SetUp() override
  {
    PrintingTests::SetUp();
    s->set_opt("produce-unsat-assumptions", "true");
    make_symbols();
  }
};

TEST_P(PrintingUnsatCoreTests, UnsatAssumptions)
{
  s->assert_formula(s->make_term(Not, b));
  ASSERT_TRUE(s->check_sat_assuming(TermVec{ b }).is_unsat());
  UnorderedTermSet assumptions;
  s->get_unsat_assumptions(assumptions);

  // MathSAT pads the parentheses of what it answers with spaces
  expect_replay({ { "unsat" }, { "(b)", "( b )" } });
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(PrintingDatatypeTests);
class PrintingDatatypeTests : public PrintingTests
{
};

TEST_P(PrintingDatatypeTests, DeclaresDatatypes)
{
  Sort intsort = s->make_sort(INT);
  DatatypeDecl listdecl = s->make_datatype_decl("list");
  DatatypeConstructorDecl nildecl = s->make_datatype_constructor_decl("nil");
  DatatypeConstructorDecl consdecl = s->make_datatype_constructor_decl("cons");
  s->add_selector(consdecl, "head", intsort);
  s->add_selector_self(consdecl, "tail");
  s->add_constructor(listdecl, nildecl);
  s->add_constructor(listdecl, consdecl);
  Sort listsort = s->make_sort(listdecl);

  // a one-element list is not nil
  Term l = s->make_symbol("l", listsort);
  Term nil =
      s->make_term(Apply_Constructor, s->get_constructor(listsort, "nil"));
  s->assert_formula(
      s->make_term(Equal,
                   l,
                   s->make_term(Apply_Constructor,
                                s->get_constructor(listsort, "cons"),
                                s->make_term(5, intsort),
                                nil)));
  s->assert_formula(
      s->make_term(Apply_Tester, s->get_tester(listsort, "nil"), l));
  ASSERT_TRUE(s->check_sat().is_unsat());

  expect_replay({ { "unsat" } });
}

INSTANTIATE_TEST_SUITE_P(,
                         PrintingTests,
                         testing::ValuesIn(replayable({})),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(,
                         PrintingBitVectorTests,
                         testing::ValuesIn(replayable({ THEORY_BV })),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(,
                         PrintingUninterpretedSortTests,
                         testing::ValuesIn(replayable({ THEORY_BV,
                                                        UNINTERP_SORT })),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(,
                         PrintingUnsatCoreTests,
                         testing::ValuesIn(replayable({ THEORY_BV,
                                                        UNSAT_CORE })),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(,
                         PrintingDatatypeTests,
                         testing::ValuesIn(replayable({ THEORY_DATATYPE })),
                         ConfigName());

}  // namespace
