/*!
 * \file z3-handle.cpp
 * \brief Tests that a handle from get_z3_solver() outlives what it came from.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * get_z3_solver() shares the Z3 solver and its context with the caller, so a
 * handle taken before reset() or before the solver is destroyed still works
 * afterwards.
 */

#include <gtest/gtest.h>
#include <z3++.h>

#include <memory>

#include "z3_solver.h"

using namespace smt;

namespace {

// asserts x = 3 for a fresh 4-bit x on s and solves
z3::check_result solve_on(z3::solver & s)
{
  z3::expr x = s.ctx().bv_const("x", 4);
  s.add(x == s.ctx().bv_val(3, 4));
  return s.check();
}

TEST(Z3Handle, UsableAfterReset)
{
  auto s = std::make_shared<Z3Solver>();
  std::shared_ptr<z3::solver> handle = s->get_z3_solver();
  s->reset();
  EXPECT_NE(s->get_z3_solver(), handle);
  EXPECT_EQ(solve_on(*handle), z3::sat);
}

TEST(Z3Handle, UsableAfterDestruction)
{
  auto s = std::make_shared<Z3Solver>();
  std::shared_ptr<z3::solver> handle = s->get_z3_solver();
  s.reset();
  EXPECT_EQ(solve_on(*handle), z3::sat);
}

}  // namespace
