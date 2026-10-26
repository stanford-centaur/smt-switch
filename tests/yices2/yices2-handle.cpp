/*!
 * \file yices2-handle.cpp
 * \brief Tests that a handle from get_context() outlives what it came from.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * get_context() shares the Yices2 context with the caller, along with the
 * Yices instance it lives in, so a handle taken before reset() or before the
 * solver is destroyed still works afterwards.
 */

#include <gtest/gtest.h>
#include <yices.h>

#include <memory>

#include "smt.h"
#include "yices2_solver.h"

using namespace smt;

namespace {

// asserts x = 3 for a fresh 4-bit x on c and solves
smt_status_t solve_on(context_t * c)
{
  type_t bv = yices_bv_type(4);
  term_t x = yices_new_uninterpreted_term(bv);
  yices_assert_formula(c, yices_eq(x, yices_bvconst_uint32(4, 3)));
  return yices_check_context(c, nullptr);
}

TEST(Yices2Handle, UsableAfterReset)
{
  auto s = std::make_shared<Yices2Solver>();
  std::shared_ptr<context_t> handle = s->get_context();
  s->reset();
  EXPECT_NE(s->get_context(), handle);
  EXPECT_EQ(solve_on(handle.get()), YICES_STATUS_SAT);
}

TEST(Yices2Handle, UsableAfterDestruction)
{
  auto s = std::make_shared<Yices2Solver>();
  std::shared_ptr<context_t> handle = s->get_context();
  s.reset();
  EXPECT_EQ(solve_on(handle.get()), YICES_STATUS_SAT);
}

}  // namespace
