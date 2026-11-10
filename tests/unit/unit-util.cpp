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

#include <gtest/gtest.h>

#include <cstddef>
#include <memory>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "available_solvers.h"
#include "datatype.h"
#include "exceptions.h"
#include "generic_sort.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"
#include "term_utils.h"
#include "utils.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitUtilTests);
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitUtilDimacsTests);
class UnitUtilDimacsTests : public ::testing::Test,
                            public ::testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    SolverEnum se = GetParam();
    SolverConfiguration sc(se, true);
    // using only logging solvers for this test because we don't want the
    // original formula to change, otherwise it might no longer be in cnf

    s = create_solver(sc);

    boolsort = s->make_sort(BOOL);
  }
  SmtSolver s;
  Sort boolsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitUtilIntTests);
class UnitUtilIntTests : public UnitUtilTests
{
 protected:
  void SetUp() override
  {
    UnitUtilTests::SetUp();
    intsort = s->make_sort(INT);
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
  ASSERT_FALSE(conjuncts.empty());

  if (GetParam().is_logging_solver)
  {
    // a logging solver kept the conjunction it was given, so each symbol is
    // its own conjunct, though the order is not maintained
    ASSERT_EQ(symbols.size(), conjuncts.size());
    UnorderedTermSet conjuncts_set(conjuncts.begin(), conjuncts.end());
    for (size_t j = 0; j < symbols.size(); ++j)
    {
      ASSERT_TRUE(conjuncts_set.find(symbols[j]) != conjuncts_set.end());
    }
    return;
  }

  // a solver that normalizes the conjunction into something else may report
  // any partition whose conjunction is the original, down to the one
  // conjunct that is the whole formula
  Term rebuilt = conjuncts[0];
  for (size_t j = 1; j < conjuncts.size(); ++j)
  {
    rebuilt = s->make_term(And, rebuilt, conjuncts[j]);
  }
  ASSERT_TRUE(round_trip_matches(GetParam(), s, rebuilt, conjunction));
}

TEST_P(UnitUtilTests, DisjunctivePartition)
{
  if (s->get_solver_enum() == BTOR)
  {
    // Boolector rewrites Ors as Not And; it is equivalent, but disjunctive
    // partition cannot see through it
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
  if (c.is_logging_solver)
  {
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

TEST_P(UnitUtilDimacsTests, cnf_to_dimacs)
{
  Term a = s->make_symbol("a", boolsort);
  Term b = s->make_symbol("b", boolsort);
  Term c = s->make_symbol("c", boolsort);
  Term d = s->make_symbol("d", boolsort);
  Term clause1 = s->make_term(Or, a, s->make_term(Or, b, s->make_term(Not, c)));
  Term clause2 = s->make_term(Or, b, s->make_term(Or, s->make_term(Not, c), d));
  Term clause3 = s->make_term(Or, d, s->make_term(Or, s->make_term(Not, c), a));
  Term cnf = s->make_term(And, clause1, s->make_term(And, clause2, clause3));
  // The terms in the output string is not in accordance with the order of the
  // input because of how to function is operating on the terms , a dry run will
  // show how the mapping of symbol to integer happens

  // Test 1

  ostringstream y;
  cnf_to_dimacs(cnf, y, s);  // cnf = ((a v b v ~c) /\ (b v ~c v d) /\ (d v ~c v
                             // a))
  string ret = y.str();
  string expected = "p cnf 4 3\n1 -2 3 0\n3 -2 4 0\n-2 4 1 0\n";
  ASSERT_TRUE(ret == expected) << ret << " " << expected << endl
                               << cnf << endl
                               << s->get_solver_enum() << endl;

  // Test 2
  Term clause4 = a;
  Term clause5 = s->make_term(Not, b);
  Term clause6 = s->make_term(Or, a, b);
  Term cnf2 = s->make_term(And, clause4, s->make_term(And, clause5, clause6));
  ostringstream y2;
  cnf_to_dimacs(cnf2, y2, s);  // cnf2 = ((a) /\ (~b) /\ (a v b))
  string ret2 = y2.str();
  string expected2 = "p cnf 2 3\n1 2 0\n-1 0\n2 0\n";
  ASSERT_TRUE(ret2 == expected2);

  // Testing an empty cnf
  Term cnf3 = s->make_term(true);
  ostringstream y3;
  cnf_to_dimacs(cnf3, y3, s);  // cnf3 = True
  string ret3 = y3.str();
  string expected3 = "p cnf 0 0\n";
  ASSERT_TRUE(ret3 == expected3) << ret3 << endl << expected3 << endl;

  // Testing empty clause
  Term clause7 = s->make_term(false);
  Term cnf4 = s->make_term(And, clause5, s->make_term(And, clause7, clause1));
  ostringstream y4;
  cnf_to_dimacs(cnf4, y4, s);  // cnf4 = ((~b) /\ (False) /\ (a v b v ~c))
  string ret4 = y4.str();
  string expected4 = "p cnf 3 3\n-1 2 3 0\n0\n-2 0\n";
  ASSERT_TRUE(ret4 == expected4) << ret4 << endl << cnf4 << endl;
}

TEST_P(UnitUtilDimacsTests, CnfToDimacsRefusesOtherFormulas)
{
  Term a = s->make_symbol("a", boolsort);
  Term b = s->make_symbol("b", boolsort);
  Term c = s->make_symbol("c", boolsort);
  Term x = s->make_symbol("x", s->make_sort(BV, 4));
  ostringstream y;
  EXPECT_THROW(cnf_to_dimacs(x, y, s), IncorrectUsageException);
  EXPECT_THROW(cnf_to_dimacs(s->make_term(Implies, a, b), y, s),
               IncorrectUsageException);
  EXPECT_THROW(
      cnf_to_dimacs(s->make_term(Or, a, s->make_term(And, b, c)), y, s),
      IncorrectUsageException);
  EXPECT_THROW(cnf_to_dimacs(s->make_term(Not, s->make_term(And, a, b)), y, s),
               IncorrectUsageException);
  EXPECT_THROW(cnf_to_dimacs(s->make_term(Not, s->make_term(Not, a)), y, s),
               IncorrectUsageException);
  EXPECT_THROW(cnf_to_dimacs(s->make_term(Or, a, s->make_term(true)), y, s),
               IncorrectUsageException);
  EXPECT_THROW(cnf_to_dimacs(s->make_term(And, a, s->make_term(true)), y, s),
               IncorrectUsageException);
}

TEST_P(UnitUtilDimacsTests, tseitin)
{
  s->set_opt("incremental", "true");
  Term p = s->make_symbol("p", boolsort);
  Term q = s->make_symbol("q", boolsort);
  Term r = s->make_symbol("r", boolsort);
  Term t = s->make_symbol("t", boolsort);

  // a=((p or q) and r) implies (not t)
  Term a = s->make_term(Implies,
                        s->make_term(And, s->make_term(Or, p, q), r),
                        s->make_term(Not, t));

  Term cnf1 = to_cnf(a, s);

  s->push();
  s->assert_formula(a);
  Result r1 = s->check_sat();
  s->pop(1);
  s->push();
  s->assert_formula(cnf1);
  Result r2 = s->check_sat();
  s->pop(1);
  ASSERT_TRUE((r1.is_sat() && r2.is_sat()) || (r1.is_unsat() && r2.is_unsat()));
  string st = cnf1->to_string();
  string expected =
      "(and tseitin_to_cnf_4 (and (or (not t) (not tseitin_to_cnf_1)) (or t "
      "tseitin_to_cnf_1) (or (not tseitin_to_cnf_2) p q) (and (or "
      "tseitin_to_cnf_2 (not p)) (or tseitin_to_cnf_2 (not q))) (or "
      "tseitin_to_cnf_3 (not tseitin_to_cnf_2) (not r)) (and (or "
      "tseitin_to_cnf_2 (not tseitin_to_cnf_3)) (or r (not tseitin_to_cnf_3))) "
      "(or (or (not tseitin_to_cnf_3) tseitin_to_cnf_1) (not "
      "tseitin_to_cnf_4)) (or tseitin_to_cnf_3 tseitin_to_cnf_4) (or (not "
      "tseitin_to_cnf_1) tseitin_to_cnf_4)))";
  ASSERT_TRUE(st == expected) << st << endl << endl << expected << endl;

  // b=Not(p xor q)
  Term b = s->make_term(Not, s->make_term(Xor, p, q));
  Term cnf2 = to_cnf(b, s);

  s->push();
  s->assert_formula(b);
  r1 = s->check_sat();
  s->pop(1);
  s->push();
  s->assert_formula(cnf2);
  r2 = s->check_sat();
  s->pop(1);
  ASSERT_TRUE((r1.is_sat() && r2.is_sat()) || (r1.is_unsat() && r2.is_unsat()));

  st = cnf2->to_string();
  expected =
      "(and tseitin_to_cnf_6 (and (or (or (not p) (not q)) (not "
      "tseitin_to_cnf_5)) (or (or p q) (not tseitin_to_cnf_5)) (or (or "
      "tseitin_to_cnf_5 q) (not p)) (or (or tseitin_to_cnf_5 p) (not q)) (or "
      "(not tseitin_to_cnf_5) (not tseitin_to_cnf_6)) (or tseitin_to_cnf_5 "
      "tseitin_to_cnf_6)))";
  ASSERT_TRUE(st == expected) << st << endl << endl << expected << endl << endl;

  // c=((not p) and p)
  Term c = s->make_term(And, s->make_term(Not, p), p);
  Term cnf3 = to_cnf(c, s);

  s->push();
  s->assert_formula(c);
  r1 = s->check_sat();
  s->pop(1);
  s->push();
  s->assert_formula(cnf3);
  r2 = s->check_sat();
  s->pop(1);
  ASSERT_TRUE((r1.is_sat() && r2.is_sat()) || (r1.is_unsat() && r2.is_unsat()));

  st = cnf3->to_string();
  expected = "(and (not p) p)";
  ASSERT_TRUE(st == expected);

  Term d1 = s->make_term(Or, p, q);
  Term d2 = s->make_term(Or, r, t);

  // d3=((p or q) and (r or t))
  Term d3 = s->make_term(And, d1, d2);

  Term cnf4 = to_cnf(d3, s);

  s->push();
  s->assert_formula(d3);
  r1 = s->check_sat();
  s->pop(1);
  s->push();
  s->assert_formula(cnf4);
  r2 = s->check_sat();
  s->pop(1);
  ASSERT_TRUE((r1.is_sat() && r2.is_sat()) || (r1.is_unsat() && r2.is_unsat()));

  st = cnf4->to_string();
  expected = "(and (or p q) (or r t))";
  ASSERT_TRUE(st == expected);
  // e=false
  Term e = s->make_term(false);
  Term cnf5 = to_cnf(e, s);

  s->push();
  s->assert_formula(e);
  r1 = s->check_sat();
  s->pop(1);
  s->push();
  s->assert_formula(cnf5);
  r2 = s->check_sat();
  s->pop(1);
  ASSERT_TRUE((r1.is_sat() && r2.is_sat()) || (r1.is_unsat() && r2.is_unsat()));

  st = cnf5->to_string();
  expected = "false";
  ASSERT_TRUE(st == expected);

  // f=true
  Term f = s->make_term(true);
  Term cnf6 = to_cnf(f, s);

  s->push();
  s->assert_formula(f);
  r1 = s->check_sat();
  s->pop(1);
  s->push();
  s->assert_formula(cnf6);
  r2 = s->check_sat();
  s->pop(1);
  ASSERT_TRUE((r1.is_sat() && r2.is_sat()) || (r1.is_unsat() && r2.is_unsat()));

  st = cnf6->to_string();
  expected = "true";
  ASSERT_TRUE(st == expected);

  TermVec vec;
  vec.push_back(p);
  vec.push_back(q);
  vec.push_back(r);
  vec.push_back(t);

  // g=OR(p, q, r, t)

  Term g = s->make_term(Or, vec);
  Term cnf7 = to_cnf(g, s);

  s->push();
  s->assert_formula(g);
  r1 = s->check_sat();
  s->pop(1);
  s->push();
  s->assert_formula(cnf7);
  r2 = s->check_sat();
  s->pop(1);
  ASSERT_TRUE((r1.is_sat() && r2.is_sat()) || (r1.is_unsat() && r2.is_unsat()));

  st = cnf7->to_string();
  expected = "(or p q r t)";
  ASSERT_TRUE(st == expected);

  Term fa = s->make_term(false);
  Term tr = s->make_term(true);

  // checking function is_cnf

  TermVec vecs;
  vecs.push_back(p);
  vecs.push_back(q);
  vecs.push_back(r);
  vecs.push_back(t);
  Term ne = s->make_term(Or, vecs);
  bool check = is_cnf(ne);
  ASSERT_TRUE(check);
  ne = s->make_term(Xor, vecs);
  check = is_cnf(ne);
  ASSERT_FALSE(check);
  ne = s->make_term(And, vecs);
  check = is_cnf(ne);
  ASSERT_TRUE(check);
  ne = s->make_term(And, s->make_term(Or, p, q), s->make_term(Or, r, t));
  check = is_cnf(ne);
  ASSERT_TRUE(check);
  ne = s->make_term(Implies, s->make_term(Or, p, q), s->make_term(Or, r, t));
  check = is_cnf(ne);
  ASSERT_FALSE(check);
  ne = s->make_term(And, s->make_term(Equal, p, q), s->make_term(Or, r, t));
  check = is_cnf(ne);
  ASSERT_FALSE(check);

  // checking elimination of true and false
  Term true_term = s->make_term(true);
  Term false_term = s->make_term(false);

  // formula=and(true, p)
  Term formula = s->make_term(And, true_term, p);
  Term as = to_cnf(formula, s);
  ASSERT_TRUE(as == p);

  // formula=and(or(p, true), or(q, false))
  formula = s->make_term(
      And, s->make_term(Or, p, true_term), s->make_term(Or, q, false_term));
  as = to_cnf(formula, s);
  ASSERT_TRUE(as == q);

  // h=((true->false)<->Or(p, q))
  Term h = s->make_term(
      Equal, s->make_term(Implies, tr, fa), s->make_term(Or, p, q));

  Term cnf8 = to_cnf(h, s);

  s->push();
  s->assert_formula(h);
  r1 = s->check_sat();
  s->pop(1);
  s->push();
  s->assert_formula(cnf8);
  r2 = s->check_sat();
  s->pop(1);
  ASSERT_TRUE((r1.is_sat() && r2.is_sat()) || (r1.is_unsat() && r2.is_unsat()));

  st = cnf8->to_string();
  expected =
      "(and tseitin_to_cnf_8 (and (or (not tseitin_to_cnf_7) p q) (and (or "
      "tseitin_to_cnf_7 (not p)) (or tseitin_to_cnf_7 (not q))) (or (not "
      "tseitin_to_cnf_7) (not tseitin_to_cnf_8)) (or tseitin_to_cnf_7 "
      "tseitin_to_cnf_8)))";
  ASSERT_TRUE(st == expected);
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ToCnf);
class ToCnf : public ::testing::Test,
              public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("incremental", "true");
    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    p = s->make_symbol("p", boolsort);
    q = s->make_symbol("q", boolsort);
    r = s->make_symbol("r", boolsort);
    x = s->make_symbol("x", bvsort);
    y = s->make_symbol("y", bvsort);
  }

  // Tseitin's fresh symbols are determined by the original ones, so the
  // CNF must agree with the formula under every assignment to p, q and r
  void expect_same_answer_per_assignment(const Term & formula, const Term & cnf)
  {
    for (int bits = 0; bits < 8; ++bits)
    {
      TermVec assumptions{ formula };
      for (int i = 0; i < 3; ++i)
      {
        Term v = TermVec{ p, q, r }[i];
        assumptions.push_back((bits >> i) & 1 ? v : s->make_term(Not, v));
      }
      bool formula_is_sat = s->check_sat_assuming(assumptions).is_sat();
      assumptions[0] = cnf;
      EXPECT_EQ(formula_is_sat, s->check_sat_assuming(assumptions).is_sat())
          << "formula: " << formula << "\ncnf: " << cnf
          << "\nassignment: " << bits;
    }
  }

  SmtSolver s;
  Sort boolsort;
  Sort bvsort;
  Term p, q, r, x, y;
};

TEST_P(ToCnf, ConnectivesKeepEveryAssignment)
{
  Term formula =
      s->make_term(And,
                   { s->make_term(Or, p, q),
                     s->make_term(Implies, q, s->make_term(Not, r)),
                     s->make_term(Xor, p, r),
                     s->make_term(Equal, p, s->make_term(Or, q, r)) });
  expect_same_answer_per_assignment(formula, to_cnf(formula, s));
}

TEST_P(ToCnf, NaryImpliesKeepsEveryAssignment)
{
  Term formula = s->make_term(
      And, s->make_term(Implies, { p, q, r }), s->make_term(Or, p, q));
  expect_same_answer_per_assignment(formula, to_cnf(formula, s));
}

TEST_P(ToCnf, NaryEqualKeepsEveryAssignment)
{
  Term formula = s->make_term(
      Or, s->make_term(Equal, { p, q, r }), s->make_term(And, p, r));
  expect_same_answer_per_assignment(formula, to_cnf(formula, s));
}

TEST_P(ToCnf, NestedNaryXorKeepsEveryAssignment)
{
  Term formula =
      s->make_term(Or, s->make_term(Xor, { p, q, r }), s->make_term(And, p, q));
  expect_same_answer_per_assignment(formula, to_cnf(formula, s));
}

TEST_P(ToCnf, IteIsKeptAsAnAtom)
{
  Term formula = s->make_term(And,
                              { s->make_term(Ite, p, q, r),
                                s->make_term(Not, p),
                                s->make_term(Not, r) });
  Term cnf = to_cnf(formula, s);
  EXPECT_TRUE(s->check_sat_assuming({ cnf }).is_unsat()) << cnf;
  expect_same_answer_per_assignment(formula, cnf);
}

TEST_P(ToCnf, DistinctIsKeptAsAnAtom)
{
  Term formula = s->make_term(And,
                              { s->make_term(Distinct, p, q),
                                s->make_term(Not, p),
                                s->make_term(Not, q) });
  Term cnf = to_cnf(formula, s);
  EXPECT_TRUE(s->check_sat_assuming({ cnf }).is_unsat()) << cnf;
  expect_same_answer_per_assignment(formula, cnf);
}

TEST_P(ToCnf, BitVectorAtomsAreKept)
{
  Term formula = s->make_term(
      And,
      s->make_term(Or, s->make_term(BVUlt, x, y), s->make_term(Equal, x, y)),
      s->make_term(BVUlt, y, x));
  Term cnf = to_cnf(formula, s);
  EXPECT_TRUE(s->check_sat_assuming({ cnf }).is_unsat()) << cnf;

  Term sat_formula = s->make_term(Or,
                                  s->make_term(BVUlt, x, y),
                                  s->make_term(Not, s->make_term(Equal, x, y)));
  Term sat_cnf = to_cnf(sat_formula, s);
  EXPECT_TRUE(s->check_sat_assuming({ sat_cnf }).is_sat()) << sat_cnf;
}

TEST_P(ToCnf, TopLevelAtomIsReturned)
{
  Term atom = s->make_term(BVUlt, x, y);
  Term cnf = to_cnf(atom, s);
  EXPECT_TRUE(s->check_sat_assuming({ cnf, atom }).is_sat()) << cnf;
  EXPECT_TRUE(
      s->check_sat_assuming({ cnf, s->make_term(Not, atom) }).is_unsat())
      << cnf;
  // a raw solver may store the atom as a connective, e.g. Yices2 builds
  // (bvult x y) as (not (bvge x y)), so only a logging solver keeps it whole
  if (GetParam().is_logging_solver)
  {
    EXPECT_EQ(cnf, atom);
  }
}

INSTANTIATE_TEST_SUITE_P(UnitUtil,
                         ToCnf,
                         testing::ValuesIn(available_solver_configurations()),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ParameterizedUnitUtilTests,
    UnitUtilTests,
    testing::ValuesIn(filter_solver_configurations({ TERMITER })));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedUnitUtilIntTests,
    UnitUtilIntTests,
    testing::ValuesIn(filter_solver_configurations({ TERMITER, THEORY_INT })));

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitUtilDimacsTests,
                         UnitUtilDimacsTests,
                         testing::ValuesIn(available_solver_enums()));

TEST(BvValueToBits, DecimalAcrossLimbs)
{
  // 2^32 - 1 and 2^32, either side of one 32-bit chunk
  EXPECT_EQ(
      bv_value_to_bits("4294967295", 10, std::make_shared<BVGenericSort>(33)),
      "0" + std::string(32, '1'));
  EXPECT_EQ(
      bv_value_to_bits("4294967296", 10, std::make_shared<BVGenericSort>(33)),
      "1" + std::string(32, '0'));
  // ten digits, so the first group of nine is a single digit
  EXPECT_EQ(
      bv_value_to_bits("1000000000", 10, std::make_shared<BVGenericSort>(30)),
      "111011100110101100101000000000");
  EXPECT_EQ(
      bv_value_to_bits(
          "000000000000000000005", 10, std::make_shared<BVGenericSort>(4)),
      "0101");
  EXPECT_EQ(bv_value_to_bits("340282366920938463463374607431768211455",
                             10,
                             std::make_shared<BVGenericSort>(128)),
            std::string(128, '1'));
}

TEST(BvValueToBits, DecimalAtTheBounds)
{
  Sort bv64 = std::make_shared<BVGenericSort>(64);
  EXPECT_EQ(bv_value_to_bits("18446744073709551615", 10, bv64),
            std::string(64, '1'));
  EXPECT_EQ(bv_value_to_bits("-9223372036854775808", 10, bv64),
            "1" + std::string(63, '0'));
  EXPECT_THROW(bv_value_to_bits("18446744073709551616", 10, bv64),
               IncorrectUsageException);
  EXPECT_THROW(bv_value_to_bits("-9223372036854775809", 10, bv64),
               IncorrectUsageException);
  // the lowest 32 bits of 2^32 are all zero, which must not read as 0
  EXPECT_THROW(
      bv_value_to_bits("4294967296", 10, std::make_shared<BVGenericSort>(8)),
      IncorrectUsageException);
}

TEST(BvValueToBits, PowerOfTwoBases)
{
  Sort bv4 = std::make_shared<BVGenericSort>(4);
  EXPECT_EQ(bv_value_to_bits("777", 8, std::make_shared<BVGenericSort>(9)),
            std::string(9, '1'));
  EXPECT_EQ(bv_value_to_bits("-1", 4, std::make_shared<BVGenericSort>(3)),
            "111");
  EXPECT_EQ(bv_value_to_bits("vV", 32, std::make_shared<BVGenericSort>(10)),
            std::string(10, '1'));
  // leading zero digits add no bits
  EXPECT_EQ(bv_value_to_bits("000000000000000f", 16, bv4), "1111");
  EXPECT_EQ(bv_value_to_bits("-1000", 2, bv4), "1000");
  EXPECT_THROW(bv_value_to_bits("10000", 2, bv4), IncorrectUsageException);
  EXPECT_THROW(bv_value_to_bits("-1001", 2, bv4), IncorrectUsageException);
  EXPECT_THROW(bv_value_to_bits("8", 8, bv4), IncorrectUsageException);
}

TEST(InternalName, KindAndIndex)
{
  EXPECT_EQ(internal_name("assump", 3), "smt_switch_internal_assump_3");
  EXPECT_TRUE(is_internal_name(internal_name("term", 1)));
  EXPECT_TRUE(is_internal_name(INTERNAL_NAME_PREFIX));
  EXPECT_FALSE(is_internal_name("smt_switch"));
  EXPECT_FALSE(is_internal_name("x_smt_switch_internal_term_1"));
}

TEST(SmtLibQuoteSymbol, SimpleSymbolStaysBare)
{
  EXPECT_EQ(smtlib_quote_symbol("x"), "x");
  EXPECT_EQ(smtlib_quote_symbol("a1"), "a1");
  EXPECT_EQ(smtlib_quote_symbol("~!@$%^&*_-+=<>.?/"), "~!@$%^&*_-+=<>.?/");
}

TEST(SmtLibQuoteSymbol, OtherSymbolGetsBars)
{
  EXPECT_EQ(smtlib_quote_symbol(""), "||");
  EXPECT_EQ(smtlib_quote_symbol("1a"), "|1a|");
  EXPECT_EQ(smtlib_quote_symbol("a b"), "|a b|");
  EXPECT_EQ(smtlib_quote_symbol("a\"b"), "|a\"b|");
  EXPECT_EQ(smtlib_quote_symbol("\xc3\xa9"), "|\xc3\xa9|");
}

TEST(SmtLibQuoteSymbol, ReservedWordGetsBars)
{
  EXPECT_EQ(smtlib_quote_symbol("let"), "|let|");
  EXPECT_EQ(smtlib_quote_symbol("par"), "|par|");
  EXPECT_EQ(smtlib_quote_symbol("NUMERAL"), "|NUMERAL|");
  EXPECT_EQ(smtlib_quote_symbol("_"), "|_|");
  EXPECT_EQ(smtlib_quote_symbol("!"), "|!|");
  EXPECT_EQ(smtlib_quote_symbol("check-sat"), "|check-sat|");
  // only the exact words are reserved
  EXPECT_EQ(smtlib_quote_symbol("lets"), "lets");
  EXPECT_EQ(smtlib_quote_symbol("Let"), "Let");
}

TEST(SmtLibUnquoteSymbol, QuotedSymbolLosesBars)
{
  EXPECT_EQ(smtlib_unquote_symbol("|a b|"), "a b");
  EXPECT_EQ(smtlib_unquote_symbol("|x|"), "x");
  EXPECT_EQ(smtlib_unquote_symbol("||"), "");
}

TEST(SmtLibUnquoteSymbol, OtherTextStaysAsIs)
{
  EXPECT_EQ(smtlib_unquote_symbol("x"), "x");
  EXPECT_EQ(smtlib_unquote_symbol(""), "");
  // a lone bar, or one at one end only, is not a quoted symbol
  EXPECT_EQ(smtlib_unquote_symbol("|"), "|");
  EXPECT_EQ(smtlib_unquote_symbol("|a"), "|a");
  EXPECT_EQ(smtlib_unquote_symbol("a|"), "a|");
}

TEST(SmtLibArithValue, IntegerStaysANumeral)
{
  EXPECT_EQ(smtlib_arith_value(INT, "5"), "5");
  EXPECT_EQ(smtlib_arith_value(INT, "-5"), "(- 5)");
  EXPECT_EQ(smtlib_arith_value(INT, "+5"), "5");
  EXPECT_EQ(smtlib_arith_value(INT, "007"), "7");
  EXPECT_EQ(smtlib_arith_value(INT, "0"), "0");
  EXPECT_EQ(smtlib_arith_value(INT, "-00"), "(- 0)");
}

TEST(SmtLibArithValue, RealGetsADecimalPoint)
{
  EXPECT_EQ(smtlib_arith_value(REAL, "5"), "5.0");
  EXPECT_EQ(smtlib_arith_value(REAL, "0.5"), "0.5");
  EXPECT_EQ(smtlib_arith_value(REAL, "-0.5"), "(- 0.5)");
}

TEST(SmtLibArithValue, DecimalGetsDigitsAroundItsPoint)
{
  EXPECT_EQ(smtlib_arith_value(REAL, ".1"), "0.1");
  EXPECT_EQ(smtlib_arith_value(REAL, "-.1"), "(- 0.1)");
  EXPECT_EQ(smtlib_arith_value(REAL, "1."), "1.0");
  EXPECT_EQ(smtlib_arith_value(REAL, "00.50"), "0.50");
}

TEST(SmtLibArithValue, FractionIsADivision)
{
  EXPECT_EQ(smtlib_arith_value(REAL, "1/2"), "(/ 1.0 2.0)");
  EXPECT_EQ(smtlib_arith_value(REAL, "-1/2"), "(- (/ 1.0 2.0))");
  EXPECT_EQ(smtlib_arith_value(REAL, "01/02"), "(/ 1.0 2.0)");
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SmtLibApplication);
class SmtLibApplication
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    intsort = s->make_sort(INT);
    x = s->make_symbol("x", intsort);
    y = s->make_symbol("y", intsort);
  }

  SmtSolver s;
  Sort intsort;
  Term x, y;
};

TEST_P(SmtLibApplication, OpThenChildren)
{
  EXPECT_EQ(smtlib_application(Op(Plus), { x, y }), "(+ x y)");
}

TEST_P(SmtLibApplication, AppliedFunctionStandsForTheOp)
{
  Term f = s->make_symbol("f", s->make_sort(FUNCTION, { intsort, intsort }));
  EXPECT_EQ(smtlib_application(Op(Apply), { f, x }), "(f x)");
}

TEST_P(SmtLibApplication, QuantifierListsItsVariableWithItsSort)
{
  Term p = s->make_param("p", intsort);
  Term body = s->make_term(Ge, p, x);
  // the children's text is given, so the body need not print alike everywhere
  auto term_text = [&](const Term & t) {
    return t == p ? string("p") : string("body");
  };
  EXPECT_EQ(smtlib_application(Op(Forall), { p, body }, term_text),
            "(forall ((p Int)) body)");
}

TEST_P(SmtLibApplication, PowerIsAProduct)
{
  EXPECT_EQ(smtlib_application(Op(Pow), { x, s->make_term(3, intsort) }),
            "(* x x x)");
}

INSTANTIATE_TEST_SUITE_P(UnitUtil,
                         SmtLibApplication,
                         testing::ValuesIn(filter_solver_configurations(
                             { THEORY_INT, QUANTIFIERS })),
                         ConfigName());

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SmtLibDeclareFun);
class SmtLibDeclareFun
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    intsort = s->make_sort(INT);
  }

  SmtSolver s;
  Sort intsort;
};

TEST_P(SmtLibDeclareFun, ConstantHasAnEmptyDomain)
{
  EXPECT_EQ(smtlib_declare_fun(s->make_symbol("x", intsort)),
            "(declare-fun x () Int)");
}

TEST_P(SmtLibDeclareFun, FunctionListsItsDomain)
{
  Sort fsort = s->make_sort(FUNCTION, { intsort, intsort, intsort });
  EXPECT_EQ(smtlib_declare_fun(s->make_symbol("f", fsort)),
            "(declare-fun f (Int Int) Int)");
}

INSTANTIATE_TEST_SUITE_P(
    UnitUtil,
    SmtLibDeclareFun,
    testing::ValuesIn(filter_solver_configurations({ THEORY_INT })),
    ConfigName());

TEST(SmtLibDeclareDatatypes, NoDatatypeIsRefused)
{
  EXPECT_THROW(smtlib_declare_datatypes({}), IncorrectUsageException);
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SmtLibDeclareDatatypes);
class SmtLibDeclareDatatypes
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    DatatypeDecl colordecl = s->make_datatype_decl("color");
    s->add_constructor(colordecl, s->make_datatype_constructor_decl("red"));
    s->add_constructor(colordecl, s->make_datatype_constructor_decl("green"));
    color = s->make_sort(colordecl);
    DatatypeDecl listdecl = s->make_datatype_decl("list");
    DatatypeConstructorDecl consdecl =
        s->make_datatype_constructor_decl("cons");
    s->add_selector(consdecl, "head", s->make_sort(INT));
    s->add_selector_self(consdecl, "tail");
    s->add_constructor(listdecl, s->make_datatype_constructor_decl("nil"));
    s->add_constructor(listdecl, consdecl);
    list = s->make_sort(listdecl);
  }

  SmtSolver s;
  Sort color, list;
};

TEST_P(SmtLibDeclareDatatypes, ListsConstructorsWithTheirSelectors)
{
  EXPECT_EQ(smtlib_declare_datatypes({ list }),
            "(declare-datatypes ((list 0)) "
            "(((nil) (cons (head Int) (tail list)))))");
}

TEST_P(SmtLibDeclareDatatypes, DeclaresSeveralTogether)
{
  EXPECT_EQ(smtlib_declare_datatypes({ color, list }),
            "(declare-datatypes ((color 0) (list 0)) "
            "(((red) (green)) ((nil) (cons (head Int) (tail list)))))");
}

TEST_P(SmtLibDeclareDatatypes, NonDatatypeIsRefused)
{
  EXPECT_THROW(smtlib_declare_datatypes({ list, s->make_sort(INT) }),
               IncorrectUsageException);
}

INSTANTIATE_TEST_SUITE_P(UnitUtil,
                         SmtLibDeclareDatatypes,
                         testing::ValuesIn(filter_solver_configurations(
                             { THEORY_INT, THEORY_DATATYPE })),
                         ConfigName());

TEST(SmtLibBenchmark, NothingToDeclare)
{
  ostringstream out;
  smtlib_benchmark(out, "QF_LIA", {});
  EXPECT_EQ(out.str(), "(set-logic QF_LIA)\n(check-sat)\n");
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SmtLibBenchmarkDeclarations);
class SmtLibBenchmarkDeclarations
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    intsort = s->make_sort(INT);
  }

  SmtSolver s;
  Sort intsort;
};

TEST_P(SmtLibBenchmarkDeclarations, DeclaresSortsThenSymbolsByName)
{
  Sort usort = s->make_sort("U", 0);
  Sort boolsort = s->make_sort(BOOL);
  Term p = s->make_symbol("p", s->make_sort(FUNCTION, { usort, boolsort }));
  Term u = s->make_symbol("u", usort);
  Term x = s->make_symbol("x", intsort);
  Term a = s->make_term(Apply, p, u);
  Term b = s->make_term(Gt, x, s->make_term(0, intsort));
  ostringstream out;
  smtlib_benchmark(out, "QF_UFLIA", { a, b });
  EXPECT_EQ(out.str(),
            "(set-logic QF_UFLIA)\n"
            "(declare-sort U 0)\n"
            "(declare-fun p (U) Bool)\n"
            "(declare-fun u () U)\n"
            "(declare-fun x () Int)\n"
            "(assert "
                + a->to_string() + ")\n(assert " + b->to_string()
                + ")\n"
                  "(check-sat)\n");
}

TEST_P(SmtLibBenchmarkDeclarations, QuotesSortNames)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the generic solver declares a sort's name to the binary "
                    "without SMT-LIB quoting";
  }
  Sort usort = s->make_sort("my sort", 0);
  Term u = s->make_symbol("u", usort);
  Term v = s->make_symbol("v", usort);
  Term eq = s->make_term(Equal, u, v);
  ostringstream out;
  smtlib_benchmark(out, "QF_UF", { eq });
  EXPECT_EQ(out.str(),
            "(set-logic QF_UF)\n"
            "(declare-sort |my sort| 0)\n"
            "(declare-fun u () |my sort|)\n"
            "(declare-fun v () |my sort|)\n"
            "(assert "
                + eq->to_string() + ")\n(check-sat)\n");
}

// SMT-LIB cannot declare two sorts with the same name, so one is renamed
TEST_P(SmtLibBenchmarkDeclarations, RenamesSortsSharingAName)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the generic solver refuses to declare a second sort with "
                    "the same name";
  }
  Sort first = s->make_sort("S", 0);
  Sort second = s->make_sort("S", 0);
  if (first == second)
  {
    GTEST_SKIP() << "this solver returns the existing sort when one with the "
                    "same name is declared again";
  }
  Term a = s->make_symbol("a", first);
  Term b = s->make_symbol("b", first);
  Term c = s->make_symbol("c", second);
  Term d = s->make_symbol("d", second);
  Term ab = s->make_term(Equal, a, b);
  Term cd = s->make_term(Equal, c, d);
  ostringstream out;
  smtlib_benchmark(out, "QF_UF", { ab, cd });
  EXPECT_EQ(out.str(),
            "(set-logic QF_UF)\n"
            "(declare-sort S 0)\n"
            "(declare-sort S_1 0)\n"
            "(declare-fun a () S_1)\n"
            "(declare-fun b () S_1)\n"
            "(declare-fun c () S)\n"
            "(declare-fun d () S)\n"
            "(assert "
                + ab->to_string() + ")\n(assert " + cd->to_string()
                + ")\n(check-sat)\n");
}

INSTANTIATE_TEST_SUITE_P(UnitUtil,
                         SmtLibBenchmarkDeclarations,
                         testing::ValuesIn(filter_solver_configurations(
                             { TERMITER, THEORY_INT, UNINTERP_SORT })),
                         ConfigName());

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SmtLibBenchmarkParamSorts);
class SmtLibBenchmarkParamSorts : public SmtLibBenchmarkDeclarations
{
};

TEST_P(SmtLibBenchmarkParamSorts, DeclaresTheSortConstructor)
{
  Sort fint = s->make_sort(s->make_sort("F", 1), { intsort });
  Term a = s->make_symbol("a", fint);
  Term b = s->make_symbol("b", fint);
  Term eq = s->make_term(Equal, a, b);
  ostringstream out;
  smtlib_benchmark(out, "ALL", { eq });
  EXPECT_EQ(out.str(),
            "(set-logic ALL)\n"
            "(declare-sort F 1)\n"
            "(declare-fun a () "
                + fint->to_string() + ")\n(declare-fun b () "
                + fint->to_string() + ")\n(assert " + eq->to_string()
                + ")\n(check-sat)\n");
}

TEST_P(SmtLibBenchmarkParamSorts, DeclaresAConstructorOnceForItsApplications)
{
  Sort f = s->make_sort("F", 1);
  Sort fint = s->make_sort(f, { intsort });
  Sort fbool = s->make_sort(f, { s->make_sort(BOOL) });
  Term ab =
      s->make_term(Equal, s->make_symbol("a", fint), s->make_symbol("b", fint));
  Term cd = s->make_term(
      Equal, s->make_symbol("c", fbool), s->make_symbol("d", fbool));
  ostringstream out;
  smtlib_benchmark(out, "ALL", { ab, cd });
  EXPECT_EQ(out.str(),
            "(set-logic ALL)\n"
            "(declare-sort F 1)\n"
            "(declare-fun a () (F Int))\n"
            "(declare-fun b () (F Int))\n"
            "(declare-fun c () (F Bool))\n"
            "(declare-fun d () (F Bool))\n"
            "(assert "
                + ab->to_string() + ")\n(assert " + cd->to_string()
                + ")\n(check-sat)\n");
}

// SMT-LIB cannot declare two sort constructors with the same name, so one is
// renamed
TEST_P(SmtLibBenchmarkParamSorts, RenamesConstructorsSharingAName)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the generic solver refuses to declare a second sort with "
                    "the same name";
  }
  Sort first = s->make_sort("F", 1);
  Sort second = s->make_sort("F", 1);
  if (first == second)
  {
    GTEST_SKIP() << "this solver returns the existing sort constructor when "
                    "one with the same name is declared again";
  }
  Sort first_int = s->make_sort(first, { intsort });
  Sort second_int = s->make_sort(second, { intsort });
  Term ab = s->make_term(
      Equal, s->make_symbol("a", first_int), s->make_symbol("b", first_int));
  Term cd = s->make_term(
      Equal, s->make_symbol("c", second_int), s->make_symbol("d", second_int));
  ostringstream out;
  smtlib_benchmark(out, "ALL", { ab, cd });
  EXPECT_EQ(out.str(),
            "(set-logic ALL)\n"
            "(declare-sort F 1)\n"
            "(declare-sort F_1 1)\n"
            "(declare-fun a () (F_1 Int))\n"
            "(declare-fun b () (F_1 Int))\n"
            "(declare-fun c () (F Int))\n"
            "(declare-fun d () (F Int))\n"
            "(assert "
                + ab->to_string() + ")\n(assert " + cd->to_string()
                + ")\n(check-sat)\n");
}

INSTANTIATE_TEST_SUITE_P(UnitUtil,
                         SmtLibBenchmarkParamSorts,
                         testing::ValuesIn(filter_solver_configurations(
                             { TERMITER, THEORY_INT, PARAM_UNINTERP_SORT })),
                         ConfigName());

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SmtLibBenchmarkDatatypes);
class SmtLibBenchmarkDatatypes : public SmtLibBenchmarkDeclarations
{
};

TEST_P(SmtLibBenchmarkDatatypes, DeclaresTheDatatypeWithItsConstructors)
{
  DatatypeDecl listdecl = s->make_datatype_decl("list");
  DatatypeConstructorDecl nildecl = s->make_datatype_constructor_decl("nil");
  DatatypeConstructorDecl consdecl = s->make_datatype_constructor_decl("cons");
  s->add_selector(consdecl, "head", intsort);
  s->add_selector_self(consdecl, "tail");
  s->add_constructor(listdecl, nildecl);
  s->add_constructor(listdecl, consdecl);
  Sort list = s->make_sort(listdecl);
  Term l = s->make_symbol("l", list);
  Term m = s->make_symbol("m", list);
  Term d = s->make_term(Distinct, l, m);
  ostringstream out;
  smtlib_benchmark(out, "ALL", { d });
  EXPECT_EQ(out.str(),
            "(set-logic ALL)\n"
            "(declare-datatypes ((list 0)) "
            "(((nil) (cons (head Int) (tail list)))))\n"
            "(declare-fun l () list)\n"
            "(declare-fun m () list)\n"
            "(assert "
                + d->to_string()
                + ")\n"
                  "(check-sat)\n");
}

TEST_P(SmtLibBenchmarkDatatypes, RefusesTwoDatatypesWithTheSameName)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the generic solver refuses to declare a second sort with "
                    "the same name";
  }
  DatatypeDecl firstdecl = s->make_datatype_decl("list");
  s->add_constructor(firstdecl, s->make_datatype_constructor_decl("one"));
  Sort first = s->make_sort(firstdecl);
  DatatypeDecl seconddecl = s->make_datatype_decl("list");
  s->add_constructor(seconddecl, s->make_datatype_constructor_decl("two"));
  Sort second = s->make_sort(seconddecl);
  if (first == second)
  {
    GTEST_SKIP() << "this solver returns the existing datatype when one with "
                    "the same name is declared again";
  }
  Term ab = s->make_term(
      Equal, s->make_symbol("a", first), s->make_symbol("b", first));
  Term cd = s->make_term(
      Equal, s->make_symbol("c", second), s->make_symbol("d", second));
  ostringstream out;
  EXPECT_THROW(smtlib_benchmark(out, "ALL", { ab, cd }),
               NotImplementedException);
}

INSTANTIATE_TEST_SUITE_P(UnitUtil,
                         SmtLibBenchmarkDatatypes,
                         testing::ValuesIn(filter_solver_configurations(
                             { TERMITER, THEORY_INT, THEORY_DATATYPE })),
                         ConfigName());

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SmtLibBenchmarkQuantifiers);
class SmtLibBenchmarkQuantifiers : public SmtLibBenchmarkDeclarations
{
};

TEST_P(SmtLibBenchmarkQuantifiers, LeavesBoundVariablesUndeclared)
{
  if (GetParam().solver_enum == Z3 && !GetParam().is_logging_solver)
  {
    GTEST_SKIP() << "Z3 cannot iterate over a quantifier's children";
  }
  Term x = s->make_symbol("x", intsort);
  Term i = s->make_param("i", intsort);
  Term forall = s->make_term(Forall, i, s->make_term(Le, i, x));
  ostringstream out;
  smtlib_benchmark(out, "ALL", { forall });
  EXPECT_EQ(out.str(),
            "(set-logic ALL)\n"
            "(declare-fun x () Int)\n"
            "(assert "
                + forall->to_string()
                + ")\n"
                  "(check-sat)\n");
}

INSTANTIATE_TEST_SUITE_P(UnitUtil,
                         SmtLibBenchmarkQuantifiers,
                         testing::ValuesIn(filter_solver_configurations(
                             { TERMITER, THEORY_INT, QUANTIFIERS })),
                         ConfigName());

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SmtLibBenchmarkRenamedSorts);
class SmtLibBenchmarkRenamedSorts : public SmtLibBenchmarkDeclarations
{
};

// a renamed sort is written by its new name inside an assertion too
TEST_P(SmtLibBenchmarkRenamedSorts, BinderUsesTheNewName)
{
  if (GetParam().solver_enum == Z3 && !GetParam().is_logging_solver)
  {
    GTEST_SKIP() << "Z3 cannot iterate over a quantifier's children";
  }
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the generic solver refuses to declare a second sort with "
                    "the same name";
  }
  Sort first = s->make_sort("S", 0);
  Sort second = s->make_sort("S", 0);
  if (first == second)
  {
    GTEST_SKIP() << "this solver returns the existing sort when one with the "
                    "same name is declared again";
  }
  Term a = s->make_symbol("a", first);
  Term y = s->make_param("y", first);
  Term forall = s->make_term(Forall, y, s->make_term(Equal, y, a));
  Term c = s->make_symbol("c", second);
  Term d = s->make_symbol("d", second);
  Term cd = s->make_term(Equal, c, d);
  ostringstream out;
  smtlib_benchmark(out, "UF", { forall, cd });
  EXPECT_EQ(out.str(),
            "(set-logic UF)\n"
            "(declare-sort S 0)\n"
            "(declare-sort S_1 0)\n"
            "(declare-fun a () S_1)\n"
            "(declare-fun c () S)\n"
            "(declare-fun d () S)\n"
            "(assert (forall (("
                + y->to_string() + " S_1)) (= " + y->to_string()
                + " a)))\n(assert " + cd->to_string() + ")\n(check-sat)\n");
}

INSTANTIATE_TEST_SUITE_P(
    UnitUtil,
    SmtLibBenchmarkRenamedSorts,
    testing::ValuesIn(filter_solver_configurations(
        { TERMITER, THEORY_INT, QUANTIFIERS, UNINTERP_SORT })),
    ConfigName());

}  // namespace
