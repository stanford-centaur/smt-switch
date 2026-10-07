/*!
 * \file yices2-params.cpp
 * \brief Yices2's make_param and the predicates that classify its result.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Yices2 does not claim QUANTIFIERS and make_term has no Forall or Exists
 * case, so a parameter cannot yet be bound through smt-switch. What is
 * checked here is that one can be built and classified, which is what
 * TermTranslator needs of it.
 */

#include <gtest/gtest.h>

#include "smt.h"
#include "yices2_factory.h"

using namespace smt;

namespace {

TEST(Yices2Params, MakeParam)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort bvsort8 = s->make_sort(BV, 8);
  Term p = s->make_param("p", bvsort8);

  EXPECT_TRUE(p->is_param());
  // a parameter is a symbol, but not a symbolic constant
  EXPECT_TRUE(p->is_symbol());
  EXPECT_FALSE(p->is_symbolic_const());
  EXPECT_TRUE(p->get_op().is_null());
  EXPECT_EQ(p->get_sort(), bvsort8);
  EXPECT_EQ(p->to_string(), "p");
}

TEST(Yices2Params, ParamIsNotASymbolicConstant)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort bvsort8 = s->make_sort(BV, 8);
  Term p = s->make_param("p", bvsort8);
  Term x = s->make_symbol("x", bvsort8);

  EXPECT_FALSE(x->is_param());
  EXPECT_TRUE(x->is_symbol());
  EXPECT_TRUE(x->is_symbolic_const());

  // two parameters of the same sort are still two terms
  EXPECT_NE(p, s->make_param("q", bvsort8));

  // and a parameter composes like any other term
  Term sum = s->make_term(BVAdd, p, x);
  EXPECT_EQ(sum->get_op(), Op(BVAdd));
}

}  // namespace
