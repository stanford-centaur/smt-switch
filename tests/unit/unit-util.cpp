/*********************                                           */
/*! \file unit-util.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for util functions
**
**
**/

#include <sstream>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"
#include "utils.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class UnitUtilTests : public ::testing::Test,
                      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    boolsort = s->make_sort(BOOL);
    for (size_t i = 0; i < 30; ++i)
    {
      symbols.push_back(s->make_symbol("x" + std::to_string(i), boolsort));
    }
  }
  SmtSolver s;
  Sort boolsort;
  TermVec symbols;
};

class UnitUtilIntTests : public UnitUtilTests
{
protected:
  void SetUp() override
  {
    UnitUtilTests::SetUp();
    intsort  = s->make_sort(INT);
  }
  Sort intsort;
};

TEST_P(UnitUtilTests, ConjunctivePartition)
{
  Term conjunction = symbols[0];
  for (size_t j = 1; j < symbols.size(); ++j)
  {
    conjunction = s->make_term(And, conjunction, symbols[j]);
  }

  TermVec conjuncts;
  // boolean argument means to include BVAnd
  // if over 1-bit variables
  // then this will work for Boolector even without logging
  conjunctive_partition(conjunction, conjuncts, true);
  ASSERT_EQ(symbols.size(), conjuncts.size());

  // order not necessarily maintained
  UnorderedTermSet conjuncts_set(conjuncts.begin(), conjuncts.end());

  for (size_t j = 0; j < symbols.size(); ++j)
  {
    ASSERT_TRUE(conjuncts_set.find(symbols[j]) != conjuncts_set.end());
  }
}

TEST_P(UnitUtilTests, DisjunctivePartition)
{
  if (s->get_solver_enum() == BTOR || s->get_solver_enum() == BZLA)
  {
    // Boolector and Bitwuzla rewrite Ors as Not And
    // it's equivalent, but disjunctive partition won't work
    return;
  }

  Term disjunction = symbols[0];
  for (size_t j = 1; j < symbols.size(); ++j)
  {
    disjunction = s->make_term(Or, disjunction, symbols[j]);
  }

  TermVec disjuncts;
  // boolean argument means to include BVOr
  // if over 1-bit variables
  // then this will work for Boolector even without logging
  disjunctive_partition(disjunction, disjuncts, true);
  ASSERT_EQ(symbols.size(), disjuncts.size());

  // order not necessarily maintained
  UnorderedTermSet disjuncts_set(disjuncts.begin(), disjuncts.end());

  for (size_t j = 0; j < symbols.size(); ++j)
  {
    ASSERT_TRUE(disjuncts_set.find(symbols[j]) != disjuncts_set.end());
  }
}

TEST_P(UnitUtilIntTests, Oracles)
{
  SolverConfiguration c = GetParam();
  // We only test get_ops and get_free_symbolic_consts
  // on logging solvers different from BTOR.
  // We only include logging solvers because otherwise
  // the operators and symbols might change due to internal rewrites.
  if (c.is_logging_solver) {
    Sort int_sort = s->make_sort(INT);
    Sort bv_sort = s->make_sort(BV, 4);
    Term int1 = s->make_symbol("int1", int_sort);
    Term bv1 = s->make_symbol("bv1", bv_sort);

    Term term1 = s->make_term(Plus, int1, int1);
    term1 = s->make_term(Mult, term1, int1);
    term1 = s->make_term(Lt, term1, int1);

    Term term2 = s->make_term(BVAdd, bv1, bv1);
    term2 = s->make_term(BVMul, term2, bv1);
    term2 = s->make_term(BVUlt, term2, bv1);

    Term term = s->make_term(And, term1, term2);

    UnorderedTermSet expected_symbols, concrete_symbols;
    expected_symbols.insert(int1);
    expected_symbols.insert(bv1);
    get_free_symbolic_consts(term, concrete_symbols);

    UnorderedOpSet expected_ops, concrete_ops;
    expected_ops.insert(Op(And));
    expected_ops.insert(Op(Plus));
    expected_ops.insert(Op(Mult));
    expected_ops.insert(Op(Lt));
    expected_ops.insert(Op(BVAdd));
    expected_ops.insert(Op(BVMul));
    expected_ops.insert(Op(BVUlt));
    get_ops(term, concrete_ops);

    ASSERT_EQ(expected_symbols, concrete_symbols);
    ASSERT_EQ(expected_ops, concrete_ops);
  }
}

TEST_P(UnitUtilTests, cnf_to_dimacs)
{
  if (s->get_solver_enum() == BZLA || s->get_solver_enum() == BTOR)
  {
    // Bitwuzla rewrite Ors as Not And
    // it's equivalent, but cnf will be converted into a non-cnf form and this
    // function uses the specific structure of cnf
    return;
  }
  boolsort = s->make_sort(BOOL);
  Term a = s->make_symbol("a", boolsort);
  Term b = s->make_symbol("b", boolsort);
  Term c = s->make_symbol("c", boolsort);
  Term d = s->make_symbol("d", boolsort);
  Term clause1 = s->make_term(Or, a, s->make_term(Or, b, s->make_term(Not, c)));
  Term clause2 = s->make_term(Or, b, s->make_term(Or, s->make_term(Not, c), d));
  Term clause3 = s->make_term(Or, d, s->make_term(Or, s->make_term(Not, c), a));
  Term cnf=s->make_term(And, clause1, s->make_term(And, clause2, clause3));
//The terms in the output string is not in accordance with the order of the input because of how to function is operating on the terms
//, a dry run will show how the mapping of symbol to integer happens

  // Test 1

  ostringstream y;
  cnf_to_dimacs(cnf, y);
  string ret = y.str();
  string ans = "p cnf 4 3\n1 -2 3 0\n3 -2 4 0\n-2 4 1 0\n";
  ASSERT_TRUE(ret == ans) << ret << " " << ans << endl << cnf << endl;

  // Test 2
  Term clause4 = a;
  Term clause5 = s->make_term(Not, b);
  Term clause6 = s->make_term(Or, a, b);
  Term cnf2 = s->make_term(And, clause4, s->make_term(And, clause5, clause6));
  ostringstream y2;
  cnf_to_dimacs(cnf2, y2);
  string ret2 = y2.str();
  string ans2 = "p cnf 2 3\n1 2 0\n-1 0\n2 0\n";
  ASSERT_TRUE(ret2 == ans2);

  // Testing an empty cnf
  Term cnf3 = s->make_term(true);
  ostringstream y3;
  cnf_to_dimacs(cnf3, y3);
  string ret3 = y3.str();
  string ans3 = "p cnf 0 0\n";
  ASSERT_TRUE(ret3 == ans3) << ret3 << endl << ans3 << endl;

  // Testing empty clause
  Term clause7 = s->make_term(false);
  Term cnf4 = s->make_term(And, clause5, s->make_term(And, clause7, clause1));
  ostringstream y4;
  cnf_to_dimacs(cnf4, y4);
  string ret4 = y4.str();
  string ans4 = "p cnf 3 3\n-1 2 3 0\n0\n-2 0\n";
  ASSERT_TRUE(ret4 == ans4) << ret4 << endl << cnf4 << endl;
}


INSTANTIATE_TEST_SUITE_P(ParameterizedUnitUtilTests,
                         UnitUtilTests,
                         testing::ValuesIn(filter_solver_configurations({ TERMITER })));

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitUtilIntTests,
                         UnitUtilIntTests,
                         testing::ValuesIn(filter_solver_configurations({ TERMITER, THEORY_INT })));

}  // namespace smt_tests
