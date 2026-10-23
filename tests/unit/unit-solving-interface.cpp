/*********************                                                        */
/*! \file unit-solving-interface.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for solving interface.
**
**
**/

#include <fstream>
#include <set>
#include <sstream>
#include <string>
#include <type_traits>
#include <utility>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "printing_solver.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

namespace {

// a range iterated only through free begin and end, found by
// argument-dependent lookup
struct FreeBeginRange
{
  TermVec terms;
};

TermVec::const_iterator begin(const FreeBeginRange & r)
{
  return r.terms.begin();
}

TermVec::const_iterator end(const FreeBeginRange & r) { return r.terms.end(); }

// What s writes to filename for an asserted x = y, or "refused" if it does
// not dump
string dump_equality(SmtSolver s, const string & filename)
{
  Sort bvsort = s->make_sort(BV, 4);
  s->assert_formula(s->make_term(
      Equal, s->make_symbol("x", bvsort), s->make_symbol("y", bvsort)));
  try
  {
    s->dump_smt2(filename);
  }
  catch (NotImplementedException &)
  {
    return "refused";
  }
  ifstream in(filename);
  stringstream contents;
  contents << in.rdbuf();
  return contents.str();
}

template <class A, class = void>
struct AcceptsAssumptions : std::false_type
{
};

template <class A>
struct AcceptsAssumptions<
    A,
    std::void_t<decltype(std::declval<AbsSmtSolver &>().check_sat_assuming(
        std::declval<const A &>()))>> : std::true_type
{
};

// a Term iterates over its children, which are not meant as assumptions
static_assert(!AcceptsAssumptions<Term>::value,
              "check_sat_assuming rejects a single Term");
static_assert(AcceptsAssumptions<TermVec>::value
                  && AcceptsAssumptions<TermList>::value
                  && AcceptsAssumptions<UnorderedTermSet>::value
                  && AcceptsAssumptions<std::set<Term>>::value
                  && AcceptsAssumptions<FreeBeginRange>::value,
              "check_sat_assuming accepts ranges of Terms");

}  // namespace

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSolveTests);
class UnitSolveTests : public ::testing::Test,
                       public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("incremental", "true");
    s->set_opt("produce-models", "true");
    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
  }
  SmtSolver s;
  Sort boolsort, bvsort;
};

TEST_P(UnitSolveTests, CheckSatAssuming)
{
  Term b1 = s->make_symbol("b1", boolsort);
  Term b2 = s->make_symbol("b2", boolsort);
  Term x = s->make_symbol("x", bvsort);

  Term nb2 = s->make_term(Not, b2);
  Term xeq0 = s->make_term(Equal, x, s->make_term(0, bvsort));
  Term nxeq0 = s->make_term(Not, xeq0);
  s->assert_formula(s->make_term(Implies, b1, xeq0));
  s->assert_formula(s->make_term(Implies, nb2, nxeq0));

  Result r = s->check_sat_assuming(TermVec{ xeq0, nb2 });
  EXPECT_TRUE(r.is_unsat());

  r = s->check_sat_assuming(TermVec{ b1, nb2 });
  EXPECT_TRUE(r.is_unsat());

  r = s->check_sat_assuming(TermList{ b1, nb2 });
  EXPECT_TRUE(r.is_unsat());

  r = s->check_sat_assuming(UnorderedTermSet{ b1, nb2 });
  EXPECT_TRUE(r.is_unsat());

  r = s->check_sat_assuming(std::set<Term>{ b1, nb2 });
  EXPECT_TRUE(r.is_unsat());

  r = s->check_sat_assuming(FreeBeginRange{ { b1, nb2 } });
  EXPECT_TRUE(r.is_unsat());
}

TEST_P(UnitSolveTests, NoAssumptions)
{
  Term b = s->make_symbol("b", boolsort);
  s->assert_formula(b);
  EXPECT_TRUE(s->check_sat_assuming(TermVec{}).is_sat());
  s->assert_formula(s->make_term(Not, b));
  EXPECT_TRUE(s->check_sat_assuming(TermVec{}).is_unsat());
}

TEST_P(UnitSolveTests, SatisfiableAssumption)
{
  Term b = s->make_symbol("b", boolsort);
  Term x = s->make_symbol("x", bvsort);
  s->assert_formula(s->make_term(
      Implies, b, s->make_term(Equal, x, s->make_term(0, bvsort))));
  // the model follows the assumption
  ASSERT_TRUE(s->check_sat_assuming(TermVec{ b }).is_sat());
  EXPECT_EQ(s->get_value(x)->to_int(), 0);
}

TEST_P(UnitSolveTests, WrappersDumpAsWrappedSolver)
{
  SolverEnum se = GetParam().solver_enum;
  string prefix = testing::TempDir() + to_string(se);
  string plain = dump_equality(create_solver(SolverConfiguration(se, false)),
                               prefix + "-plain.smt2");
  // a logging configuration wraps the plain solver in a LoggingSolver
  EXPECT_EQ(dump_equality(create_solver(GetParam()), prefix + "-param.smt2"),
            plain);
  ostringstream printed;
  EXPECT_EQ(
      dump_equality(create_printing_solver(create_solver(GetParam()), &printed),
                    prefix + "-printing.smt2"),
      plain);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedUnitSolveTests,
    UnitSolveTests,
    testing::ValuesIn(filter_solver_configurations({ TERMITER })));

TEST(Result, ComparesByResultType)
{
  EXPECT_EQ(Result(SAT), Result(SAT, "another explanation"));
  EXPECT_FALSE(Result(SAT) != Result(SAT, "another explanation"));
  EXPECT_NE(Result(SAT), Result(UNSAT));
  EXPECT_NE(Result(UNKNOWN), Result());
}

}  // namespace smt_tests
