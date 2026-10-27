/*!
 * \file bzla-handle.cpp
 * \brief Tests that a handle from get_bitwuzla() outlives what it came from.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * get_bitwuzla() shares the Bitwuzla instance and its term manager with the
 * caller, so a handle taken before reset() or before the solver is destroyed
 * still works afterwards.
 */

// Bitwuzla's header before 0.8.0 needs <cstdint> first.
#ifdef SMT_SWITCH_BITWUZLA_NEEDS_CSTDINT
#include <cstdint>
#endif
#include <bitwuzla/cpp/bitwuzla.h>
#include <gtest/gtest.h>

#include <memory>
#include <string>
#include <vector>

#include "bitwuzla_solver.h"

using namespace smt;

namespace {

// asserts x = 3 for a fresh 4-bit x on b and solves
bitwuzla::Result solve_on(bitwuzla::Bitwuzla & b)
{
  bitwuzla::TermManager & tm = b.term_mgr();
  bitwuzla::Sort bv = tm.mk_bv_sort(4);
  bitwuzla::Term x = tm.mk_const(bv, "x");
  b.assert_formula(
      tm.mk_term(bitwuzla::Kind::EQUAL, { x, tm.mk_bv_value_uint64(bv, 3) }));
  return b.check_sat();
}

TEST(BzlaHandle, UsableAfterReset)
{
  auto s = std::make_shared<BzlaSolver>();
  std::shared_ptr<bitwuzla::Bitwuzla> handle = s->get_bitwuzla();
  s->reset();
  EXPECT_NE(s->get_bitwuzla(), handle);
  EXPECT_EQ(solve_on(*handle), bitwuzla::Result::SAT);
}

TEST(BzlaHandle, UsableAfterDestruction)
{
  auto s = std::make_shared<BzlaSolver>();
  std::shared_ptr<bitwuzla::Bitwuzla> handle = s->get_bitwuzla();
  s.reset();
  EXPECT_EQ(solve_on(*handle), bitwuzla::Result::SAT);
}

}  // namespace
