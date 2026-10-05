/*********************                                                        */
/*! \file yices2-polynomial.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
**
**
**/

#include <gtest/gtest.h>

#include <memory>
#include <vector>

#include "smt.h"
#include "yices.h"
#include "yices2_factory.h"
#include "yices2_sort.h"
#include "yices2_term.h"
// after a full installation
// #include "smt-switch/msat_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;

/* Yices keeps a sum or a product as a polynomial rather than as an
 * application, so several of these children do not exist as Yices terms
 * until Yices2TermIter builds them. Rebuilding the term from the op and the
 * children it reports is the invariant that matters, since that is what a
 * walker or a translator does, and it does not depend on the order Yices
 * chose for the components. The solver is deliberately not a logging one,
 * so the backend's own iteration is what runs.
 */
TEST(Yices2Polynomial, RebuildFromIteratedChildren)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort intsort = s->make_sort(INT);
  Sort bvsort = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term bx = s->make_symbol("bx", bvsort);
  Term by = s->make_symbol("by", bvsort);
  Term two = s->make_term("2", intsort);
  Term minus_one = s->make_term("-1", intsort);
  Term four = s->make_term("4", intsort);

  TermVec cases;
  // an arithmetic sum of two monomials, one with a coefficient
  cases.push_back(s->make_term(Plus, s->make_term(Mult, two, x), y));
  // a single monomial, which Yices still reports as a sum and get_op reads
  // as Mult, so its children are the coefficient and the term
  cases.push_back(s->make_term(Mult, minus_one, y));
  // a constant summand, which arrives with no term of its own
  cases.push_back(s->make_term(Plus, x, two));
  // a power product, whose exponent is not a term either
  cases.push_back(s->make_term(Pow, x, four));
  // a bit-vector sum, with a bit-vector coefficient
  cases.push_back(s->make_term(BVAdd, bx, s->make_term(BVMul, by, bx)));
  // and an ordinary composite, whose children Yices does store
  cases.push_back(s->make_term(Equal, x, y));
  cases.push_back(s->make_term(Ite, s->make_term(Equal, x, y), x, y));

  for (const Term & t : cases)
  {
    TermVec children(t->begin(), t->end());
    EXPECT_GT(children.size(), 0u) << t;
    for (const Term & child : children)
    {
      EXPECT_TRUE(child) << t;
    }
    EXPECT_EQ(s->make_term(t->get_op(), children), t) << t;
  }
}

TEST(Yices2Polynomial, PolynomialConstraints)
{
  SmtSolver s = Yices2SolverFactory::create(true);
  s->set_opt("produce-models", "true");
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term y = s->make_symbol("y", bvsort8);
  Term z = s->make_symbol("z", bvsort8);

  Term a = s->make_symbol("a", s->make_sort(INT));
  Term b = s->make_symbol("b", s->make_sort(INT));
  Term c = s->make_symbol("c", s->make_sort(INT));

  // every constraint below is satisfiable: the bit-vectors and b can be
  // zero with a = -1 or 0, or b = 12 and d = 88; the last one forces b = 45
  auto expect_sat = [&s](const Term & constraint) {
    s->push();
    s->assert_formula(constraint);
    EXPECT_TRUE(s->check_sat().is_sat()) << constraint;
    s->pop();
  };

  Term constraint;

  constraint = s->make_term(
      Equal, c, s->make_term(Pow, b, s->make_term("4", s->make_sort(INT))));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, b));
  expect_sat(constraint);

  constraint = s->make_term(Equal, z, s->make_term(BVMul, x, y));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, b));
  expect_sat(constraint);

  constraint = s->make_term(Equal, z, s->make_term(BVAdd, x, y));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, b));
  expect_sat(constraint);

  constraint =
      s->make_term(Equal, z, s->make_term(BVAdd, x, s->make_term(BVMul, y, z)));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, b));
  expect_sat(constraint);

  constraint =
      s->make_term(Equal, z, s->make_term(BVAdd, x, s->make_term(BVMul, y, z)));
  constraint = s->make_term(
      And,
      constraint,
      s->make_term(Equal,
                   a,
                   s->make_term(Pow, b, s->make_term("4", s->make_sort(INT)))));
  expect_sat(constraint);

  Term bv_sum = s->make_term(BVAdd, x, s->make_term(BVMul, y, z));
  EXPECT_EQ(bv_sum->get_sort(), bvsort8);
  EXPECT_EQ(bv_sum->get_op(), BVAdd);
  constraint = s->make_term(Equal, z, bv_sum);

  c = s->make_term("3", s->make_sort(INT));

  constraint = s->make_term(
      And, constraint, s->make_term(Equal, a, s->make_term(Pow, b, c)));
  expect_sat(constraint);

  Term d = s->make_symbol("d", s->make_sort(INT));

  constraint = s->make_term(
      Equal, s->make_term("100", s->make_sort(INT)), s->make_term(Plus, b, d));

  constraint =
      s->make_term(And,
                   constraint,
                   s->make_term(Ge, b, s->make_term("12", s->make_sort(INT))));
  expect_sat(constraint);

  constraint = s->make_term(
      Equal,
      s->make_term("100", s->make_sort(INT)),
      s->make_term(Plus, b, s->make_term("55", s->make_sort(INT))));

  constraint =
      s->make_term(And,
                   constraint,
                   s->make_term(Ge, b, s->make_term("12", s->make_sort(INT))));

  s->assert_formula(constraint);
  ASSERT_TRUE(s->check_sat().is_sat());
  EXPECT_EQ(s->get_value(b)->to_int(), 45);
}
