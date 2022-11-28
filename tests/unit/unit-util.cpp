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

TEST_P(UnitUtilDimacsTests, cnf_to_dimacs)
{
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
  cnf_to_dimacs(cnf, y);  // cnf = ((a v b v ~c) /\ (b v ~c v d) /\ (d v ~c v
                          // a))
  string ret = y.str();
  string ans = "p cnf 4 3\n1 -2 3 0\n3 -2 4 0\n-2 4 1 0\n";
  ASSERT_TRUE(ret == ans) << ret << " " << ans << endl
                          << cnf << endl
                          << s->get_solver_enum() << endl;

  // Test 2
  Term clause4 = a;
  Term clause5 = s->make_term(Not, b);
  Term clause6 = s->make_term(Or, a, b);
  Term cnf2 = s->make_term(And, clause4, s->make_term(And, clause5, clause6));
  ostringstream y2;
  cnf_to_dimacs(cnf2, y2);  // cnf2 = ((a) /\ (~b) /\ (a v b))
  string ret2 = y2.str();
  string ans2 = "p cnf 2 3\n1 2 0\n-1 0\n2 0\n";
  ASSERT_TRUE(ret2 == ans2);

  // Testing an empty cnf
  Term cnf3 = s->make_term(true);
  ostringstream y3;
  cnf_to_dimacs(cnf3, y3);  // cnf3 = True
  string ret3 = y3.str();
  string ans3 = "p cnf 0 0\n";
  ASSERT_TRUE(ret3 == ans3) << ret3 << endl << ans3 << endl;

  // Testing empty clause
  Term clause7 = s->make_term(false);
  Term cnf4 = s->make_term(And, clause5, s->make_term(And, clause7, clause1));
  ostringstream y4;
  cnf_to_dimacs(cnf4, y4);  // cnf4 = ((~b) /\ (False) /\ (a v b v ~c))
  string ret4 = y4.str();
  string ans4 = "p cnf 3 3\n-1 2 3 0\n0\n-2 0\n";
  ASSERT_TRUE(ret4 == ans4) << ret4 << endl << cnf4 << endl;
}

TEST_P(UnitUtilDimacsTests, tseitin)
{
  s->set_opt("incremental", "true");
  Term p = s->make_symbol("p", boolsort);
  Term q = s->make_symbol("q", boolsort);
  Term r = s->make_symbol("r", boolsort);
  Term t = s->make_symbol("t", boolsort);
  
  //a=((p or q) and r) implies (not t)
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
  string ans =
      "(and tseitin_to_cnf_4 (and (or (not t) (not tseitin_to_cnf_1)) (or t "
      "tseitin_to_cnf_1) (or (not tseitin_to_cnf_2) p q) (and (or "
      "tseitin_to_cnf_2 (not p)) (or tseitin_to_cnf_2 (not q))) (or "
      "tseitin_to_cnf_3 (not tseitin_to_cnf_2) (not r)) (and (or "
      "tseitin_to_cnf_2 (not tseitin_to_cnf_3)) (or r (not tseitin_to_cnf_3))) "
      "(or (or (not tseitin_to_cnf_3) tseitin_to_cnf_1) (not "
      "tseitin_to_cnf_4)) (or tseitin_to_cnf_3 tseitin_to_cnf_4) (or (not "
      "tseitin_to_cnf_1) tseitin_to_cnf_4)))";
  ASSERT_TRUE(st == ans) << st << endl << endl << ans << endl;

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
  ans =
      "(and tseitin_to_cnf_6 (and (or (or (not p) (not q)) (not "
      "tseitin_to_cnf_5)) (or (or p q) (not tseitin_to_cnf_5)) (or (or "
      "tseitin_to_cnf_5 q) (not p)) (or (or tseitin_to_cnf_5 p) (not q)) (or "
      "(not tseitin_to_cnf_5) (not tseitin_to_cnf_6)) (or tseitin_to_cnf_5 "
      "tseitin_to_cnf_6)))";
  ASSERT_TRUE(st == ans) << st << endl << endl << ans << endl << endl;

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
  ans = "(and (not p) p)";
  ASSERT_TRUE(st == ans);

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
  ans = "(and (or p q) (or r t))";
  ASSERT_TRUE(st == ans);
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
  ans = "false";
  ASSERT_TRUE(st == ans);

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
  ans = "true";
  ASSERT_TRUE(st == ans);

  std::vector<Term> vec;
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
  ans = "(or p q r t)";
  ASSERT_TRUE(st == ans);

  Term fa = s->make_term(false);
  Term tr = s->make_term(true);

  // cheking function is_cnf

  std::vector<Term> vecs;
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
  Term tru = s->make_term(true);
  Term fal = s->make_term(false);

  // formula=and(true, p)
  Term formula = s->make_term(And, tru, p);
  Term as = to_cnf(formula, s);
  ASSERT_TRUE(as == p);

  // formula=and(or(p, true), or(q, false))
  formula =
      s->make_term(And, s->make_term(Or, p, tru), s->make_term(Or, q, fal));
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
  ans =
      "(and tseitin_to_cnf_8 (and (or (not tseitin_to_cnf_7) p q) (and (or "
      "tseitin_to_cnf_7 (not p)) (or tseitin_to_cnf_7 (not q))) (or (not "
      "tseitin_to_cnf_7) (not tseitin_to_cnf_8)) (or tseitin_to_cnf_7 "
      "tseitin_to_cnf_8)))";
  ASSERT_TRUE(st == ans);
}


INSTANTIATE_TEST_SUITE_P(ParameterizedUnitUtilTests,
                         UnitUtilTests,
                         testing::ValuesIn(filter_solver_configurations({ TERMITER })));

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitUtilIntTests,
                         UnitUtilIntTests,
                         testing::ValuesIn(filter_solver_configurations({ TERMITER, THEORY_INT })));

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitUtilDimacsTests,
                         UnitUtilDimacsTests,
                         testing::ValuesIn(available_solver_enums()));

}  // namespace smt_tests
