/*!
 * \file cvc5-handle.cpp
 * \brief Tests that handles from get_cvc5_solver() and get_term_manager()
 * outlive what they came from.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * get_cvc5_solver() and get_term_manager() share the cvc5 solver and term
 * manager with the caller, so handles taken before reset() or before the
 * solver is destroyed still work afterwards.
 */

#include <cvc5/cvc5.h>
#include <gtest/gtest.h>

#include <memory>

#include "cvc5_solver.h"
#include "smt.h"

using namespace smt;

namespace {

// asserts x = 3 for a fresh 4-bit x on s, whose terms tm makes, and solves
cvc5::Result solve_on(cvc5::TermManager & tm, cvc5::Solver & s)
{
  cvc5::Sort bv = tm.mkBitVectorSort(4);
  cvc5::Term x = tm.mkConst(bv, "x");
  s.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, { x, tm.mkBitVector(4, 3) }));
  return s.checkSat();
}

TEST(Cvc5Handle, UsableAfterReset)
{
  auto s = std::make_shared<Cvc5Solver>();
  std::shared_ptr<cvc5::TermManager> tm = s->get_term_manager();
  std::shared_ptr<cvc5::Solver> handle = s->get_cvc5_solver();
  s->reset();
  EXPECT_NE(s->get_cvc5_solver(), handle);
  EXPECT_TRUE(solve_on(*tm, *handle).isSat());
}

TEST(Cvc5Handle, UsableAfterDestruction)
{
  auto s = std::make_shared<Cvc5Solver>();
  std::shared_ptr<cvc5::TermManager> tm = s->get_term_manager();
  std::shared_ptr<cvc5::Solver> handle = s->get_cvc5_solver();
  s.reset();
  EXPECT_TRUE(solve_on(*tm, *handle).isSat());
}

}  // namespace
