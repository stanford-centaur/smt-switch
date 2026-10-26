/*!
 * \file msat-handle.cpp
 * \brief Tests that a handle from get_msat_env() outlives what it came from.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * get_msat_env() shares the MathSAT environment with the caller, so a handle
 * taken before reset() or before the solver is destroyed still works
 * afterwards.
 */

#include <gtest/gtest.h>
#include <mathsat.h>

#include <memory>

#include "msat_solver.h"
#include "smt.h"

using namespace smt;

namespace {

// asserts x = 3 for a fresh 4-bit x on e and solves
msat_result solve_on(msat_env e)
{
  msat_type bv = msat_get_bv_type(e, 4);
  msat_term x = msat_make_constant(e, msat_declare_function(e, "x", bv));
  msat_term three = msat_make_bv_number(e, "3", 4, 10);
  msat_assert_formula(e, msat_make_equal(e, x, three));
  return msat_solve(e);
}

TEST(MsatHandle, UsableAfterReset)
{
  auto s = std::make_shared<MsatSolver>();
  std::shared_ptr<msat_env> handle = s->get_msat_env();
  s->reset();
  EXPECT_NE(s->get_msat_env(), handle);
  EXPECT_EQ(solve_on(*handle), MSAT_SAT);
}

TEST(MsatHandle, UsableAfterDestruction)
{
  auto s = std::make_shared<MsatSolver>();
  std::shared_ptr<msat_env> handle = s->get_msat_env();
  s.reset();
  EXPECT_EQ(solve_on(*handle), MSAT_SAT);
}

}  // namespace
