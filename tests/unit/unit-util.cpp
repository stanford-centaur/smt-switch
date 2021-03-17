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

#include <utility>
#include <vector>

#include "utils.h"

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

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


INSTANTIATE_TEST_SUITE_P(ParameterizedUnitUtilTests,
                         UnitUtilTests,
                         testing::ValuesIn(filter_solver_configurations({ TERMITER })));

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitUtilIntTests,
                         UnitUtilIntTests,
                         testing::ValuesIn(filter_solver_configurations({ TERMITER, THEORY_INT })));

}  // namespace smt_tests
