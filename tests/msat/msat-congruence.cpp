/*!
 * \file msat-congruence.cpp
 * \brief Tests that MathSAT's congruences in interpolants read as divisible.
 * \author Po-Chun Chien
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include <gtest/gtest.h>

#include <string>

#include "interpolating_solver.h"
#include "msat_factory.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"
#include "term_translator.h"
#include "utils.h"

using namespace smt;

namespace {

TEST(MsatCongruence, InterpolantReadsAsDivisible)
{
  // A gives x the parity a and B the other one, which MathSAT interpolates
  // with the congruence x = a mod 2, i.e. (_ divisible 2) of x - a. For a = 1,
  // reading x alone would make the interpolant say that x is even.
  for (int a : { 0, 1 })
  {
    SCOPED_TRACE("x = " + std::to_string(a) + " mod 2 in A");
    SmtInterpolator itp = MsatSolverFactory::create_interpolating_solver();
    Sort intsort = itp->make_sort(INT);
    Term x = itp->make_symbol("x", intsort);
    Term y = itp->make_symbol("y", intsort);
    Term z = itp->make_symbol("z", intsort);
    Term two = itp->make_term(2, intsort);
    Term A = itp->make_term(
        Equal,
        x,
        itp->make_term(
            Plus, itp->make_term(Mult, two, y), itp->make_term(a, intsort)));
    Term B = itp->make_term(Equal,
                            x,
                            itp->make_term(Plus,
                                           itp->make_term(Mult, two, z),
                                           itp->make_term(1 - a, intsort)));
    Term I;
    ASSERT_TRUE(itp->get_interpolant(A, B, I).is_unsat());
    UnorderedOpSet ops;
    get_ops(I, ops);
    EXPECT_EQ(ops.count(Op(Divisible, 2)), 1) << I;

    // a solver can take the interpolant over, as an engine does, and it is
    // still one there: A implies it and it contradicts B
    SmtSolver s = MsatSolverFactory::create(false);
    TermTranslator to_s(s);
    Term I_s = to_s.transfer_term(I, BOOL);
    s->push();
    s->assert_formula(to_s.transfer_term(A, BOOL));
    s->assert_formula(s->make_term(Not, I_s));
    EXPECT_TRUE(s->check_sat().is_unsat()) << I;
    s->pop();
    s->push();
    s->assert_formula(I_s);
    s->assert_formula(to_s.transfer_term(B, BOOL));
    EXPECT_TRUE(s->check_sat().is_unsat()) << I;
    s->pop();
  }
}

}  // namespace
