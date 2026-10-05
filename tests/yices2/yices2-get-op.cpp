/*!
 * \file yices2-get-op.cpp
 * \brief Yices2's get_op on the shapes its term representation hides.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * These use a non-logging solver, so the backend's own get_op and iteration
 * are what run rather than the op and children a LoggingTerm recorded.
 */

#include <gtest/gtest.h>

#include "smt.h"
#include "yices2_factory.h"

using namespace smt;

namespace {

TermVec children_of(Term term)
{
  TermVec children;
  for (auto child : term)
  {
    children.push_back(child);
  }
  return children;
}

// Yices has no extract constructor: it stores (_ extract high low) as an
// array of the individual bits, which get_op has to read back.
TEST(Yices2GetOp, ExtractReadsBackAsExtract)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);

  Op extract = Op(Extract, 5, 2);
  Term extracted = s->make_term(extract, x);
  EXPECT_EQ(extracted->get_op(), extract);
  // the bits are not the children smt-switch sees: an extract has one
  EXPECT_EQ(children_of(extracted), TermVec{ x });
  EXPECT_EQ(s->make_term(extracted->get_op(), children_of(extracted)),
            extracted);

  // one bit wide, so the array holds a single bit
  Op one_bit = Op(Extract, 3, 3);
  Term bit = s->make_term(one_bit, x);
  EXPECT_EQ(bit->get_op(), one_bit);
  EXPECT_EQ(children_of(bit), TermVec{ x });
  EXPECT_EQ(s->make_term(bit->get_op(), children_of(bit)), bit);

  // the whole width is the identity, and Yices returns the argument itself
  EXPECT_EQ(s->make_term(Op(Extract, 7, 0), x), x);
}

/* Reading a bit array back as an extract cannot mistake some other operator
 * for one, because Yices canonicalises into that array: everything below
 * covers the same consecutive bits of one bit-vector and so is not merely
 * equal to the extract, it is the same term, with whatever the caller
 * originally wrote already erased.
 */
TEST(Yices2GetOp, WhatCanonicalisesIntoAnExtract)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term extracted = s->make_term(Op(Extract, 5, 2), x);

  // a concatenation of two adjacent slices
  EXPECT_EQ(s->make_term(Concat,
                         s->make_term(Op(Extract, 5, 4), x),
                         s->make_term(Op(Extract, 3, 2), x)),
            extracted);

  // an extract of an extract, whose indices are relative to the inner one
  EXPECT_EQ(s->make_term(Op(Extract, 1, 0), extracted),
            s->make_term(Op(Extract, 3, 2), x));

  // an extract of a constant shift, which lands on a shifted run
  Term shifted = s->make_term(BVLshr, x, s->make_term(2, bvsort8));
  EXPECT_EQ(s->make_term(Op(Extract, 5, 2), shifted),
            s->make_term(Op(Extract, 7, 4), x));

  // but a gap in the bits is a concatenation and has to keep reading as one
  Term with_gap = s->make_term(Concat,
                               s->make_term(Op(Extract, 7, 4), x),
                               s->make_term(Op(Extract, 1, 0), x));
  EXPECT_EQ(with_gap->get_op(), Op(Concat));
}

// A declared constant, array or function has no children, so no op either.
TEST(Yices2GetOp, SymbolHasNoOp)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term f =
      s->make_symbol("f", s->make_sort(FUNCTION, SortVec{ bvsort8, bvsort8 }));
  Term a = s->make_symbol("a", s->make_sort(ARRAY, bvsort8, bvsort8));

  for (Term symbol : TermVec{ x, f, a })
  {
    EXPECT_TRUE(symbol->get_op().is_null()) << symbol;
    EXPECT_TRUE(symbol->is_symbol()) << symbol;
    EXPECT_TRUE(children_of(symbol).empty()) << symbol;
  }

  // applying one of them is what carries the op, and the application is not
  // itself a symbol
  Term applied = s->make_term(Apply, f, x);
  EXPECT_EQ(applied->get_op(), Op(Apply));
  EXPECT_FALSE(applied->is_symbol());
  EXPECT_FALSE(applied->is_symbolic_const());
  EXPECT_EQ(children_of(applied), (TermVec{ f, x }));
  EXPECT_EQ(s->make_term(applied->get_op(), children_of(applied)), applied);

  Term selected = s->make_term(Select, a, x);
  EXPECT_EQ(selected->get_op(), Op(Select));
  EXPECT_FALSE(selected->is_symbol());
  EXPECT_EQ(children_of(selected), (TermVec{ a, x }));
  EXPECT_EQ(s->make_term(selected->get_op(), children_of(selected)), selected);
}

/* Every op Yices builds out of a constructor of its own has to report that
 * op back. A term with children and no op is one a walker or a translator
 * cannot rebuild, and `src/term_translator.cpp` asserts against it.
 */
TEST(Yices2GetOp, CompositeTermsReportTheirOp)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term a = s->make_symbol("a", s->make_sort(ARRAY, bvsort8, bvsort8));
  // a real, since Yices folds the floor and the integrality test of a term
  // already known to be an integer
  Term r = s->make_symbol("r", s->make_sort(REAL));

  // Yices keeps a store as a function update
  Term stored = s->make_term(Store, a, x, s->make_term(7, bvsort8));
  EXPECT_EQ(stored->get_op(), Op(Store));

  // and reaches these two through its floor and integrality constructors
  EXPECT_EQ(s->make_term(To_Int, r)->get_op(), Op(To_Int));
  EXPECT_EQ(s->make_term(Is_Int, r)->get_op(), Op(Is_Int));
}

/* An array is a function to Yices, so a child's kind cannot be had by
 * asking Yices about it; the term being iterated is what knows.
 */
TEST(Yices2GetOp, IterationKeepsAnArrayAnArray)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort bvsort8 = s->make_sort(BV, 8);
  Sort arrsort = s->make_sort(ARRAY, bvsort8, bvsort8);
  Sort funsort = s->make_sort(FUNCTION, SortVec{ bvsort8, bvsort8 });
  Term x = s->make_symbol("x", bvsort8);
  Term a = s->make_symbol("a", arrsort);
  Term f = s->make_symbol("f", funsort);

  for (Term over_array :
       TermVec{ s->make_term(Select, a, x), s->make_term(Store, a, x, x) })
  {
    EXPECT_EQ(children_of(over_array).at(0)->get_sort(), arrsort) << over_array;
  }

  Term applied = s->make_term(Apply, f, x);
  EXPECT_EQ(children_of(applied).at(0)->get_sort(), funsort);
}

}  // namespace
