/*!
 * \file btor-handle.cpp
 * \brief Tests that a handle from get_btor() outlives what it came from.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * get_btor() shares the Boolector instance with the caller, so a handle
 * taken before reset() or before the solver is destroyed still works
 * afterwards, on an instance the solver no longer uses.
 */

#include <boolector.h>
#include <gtest/gtest.h>

#include <memory>

#include "boolector_solver.h"
#include "smt.h"

using namespace smt;

namespace {

// asserts x = 3 for a fresh 4-bit x on b and solves
int32_t solve_on(Btor * b)
{
  BoolectorSort bv = boolector_bitvec_sort(b, 4);
  BoolectorNode * x = boolector_var(b, bv, "x");
  BoolectorNode * three = boolector_unsigned_int(b, 3, bv);
  BoolectorNode * eq = boolector_eq(b, x, three);
  boolector_assert(b, eq);
  int32_t result = boolector_sat(b);
  boolector_release(b, eq);
  boolector_release(b, three);
  boolector_release(b, x);
  boolector_release_sort(b, bv);
  return result;
}

TEST(BtorHandle, UsableAfterReset)
{
  auto s = std::make_shared<BoolectorSolver>();
  std::shared_ptr<Btor> handle = s->get_btor();
  s->reset();
  EXPECT_NE(s->get_btor(), handle);
  EXPECT_EQ(solve_on(handle.get()), BOOLECTOR_SAT);
}

TEST(BtorHandle, UsableAfterDestruction)
{
  auto s = std::make_shared<BoolectorSolver>();
  s->set_opt("time-limit", "10");
  std::shared_ptr<Btor> handle = s->get_btor();
  s.reset();
  EXPECT_EQ(solve_on(handle.get()), BOOLECTOR_SAT);
}

}  // namespace
