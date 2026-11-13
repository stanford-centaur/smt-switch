/*!
 * \file z3-quantifier.cpp
 * \brief Tests the children of a Z3 quantifier binding several variables
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * make_term binds one param per quantifier, but a Z3 term wrapped from Z3
 * itself can bind several, which smt-switch lists as nested quantifiers.
 */
#include <gtest/gtest.h>
#include <z3++.h>

#include <memory>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/z3_context.h"
#include "smt-switch/z3_solver.h"
#include "smt-switch/z3_term.h"

using namespace smt;

namespace {

TEST(Z3Quantifier, BindingSeveralListsTheFirstThenTheRest)
{
  auto s = std::make_shared<Z3Solver>();
  Sort bv = s->make_sort(BV, 4);
  Term i = s->make_param("i", bv);
  Term j = s->make_param("j", bv);
  Term x = s->make_symbol("x", bv);
  Term body = s->make_term(BVUle, s->make_term(BVAdd, i, j), x);

  auto ctx = std::static_pointer_cast<Z3Context>(s->get_z3_context());
  z3::expr_vector bound(*ctx);
  bound.push_back(std::static_pointer_cast<Z3Term>(i)->get_z3_expr());
  bound.push_back(std::static_pointer_cast<Z3Term>(j)->get_z3_expr());
  Term both = std::make_shared<Z3Term>(
      ctx,
      z3::forall(bound, std::static_pointer_cast<Z3Term>(body)->get_z3_expr()));

  EXPECT_EQ(both->get_op(), Forall);
  TermVec children(both->begin(), both->end());
  ASSERT_EQ(children.size(), 2u);
  EXPECT_EQ(children[0], i);
  EXPECT_EQ(children[1], s->make_term(Forall, j, body));
}

}  // namespace
