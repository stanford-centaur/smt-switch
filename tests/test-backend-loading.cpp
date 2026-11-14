/*!
 * \file test-backend-loading.cpp
 * \brief Tests that a shared libsmt-switch loads backends a program does
 *        not link
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * This program links libsmt-switch alone, so every backend it reaches is
 * one create_solver loaded.
 */
#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/solver_factory.h"

using namespace smt;

namespace {

TEST(BackendLoading, FindsEveryConfiguredBackend)
{
  std::vector<SolverEnum> expected;
#ifdef BUILD_BTOR
  expected.push_back(BTOR);
#endif
#ifdef BUILD_BITWUZLA
  expected.push_back(BZLA);
#endif
#ifdef BUILD_CVC5
  expected.push_back(CVC5);
#endif
#ifdef BUILD_MSAT
  expected.push_back(MSAT);
#endif
#ifdef BUILD_YICES2
  expected.push_back(YICES2);
#endif
#ifdef BUILD_Z3
  expected.push_back(Z3);
#endif
  std::vector<SolverEnum> available = available_solver_enums();
  std::sort(expected.begin(), expected.end());
  std::sort(available.begin(), available.end());
  EXPECT_EQ(available, expected);
  for (SolverEnum se : available)
  {
    EXPECT_EQ(create_solver(se, false)->get_solver_enum(), se);
  }
}

}  // namespace
