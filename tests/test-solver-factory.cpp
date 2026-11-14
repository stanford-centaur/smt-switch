/*!
 * \file test-solver-factory.cpp
 * \brief Tests creating solvers and interpolators from their solver enum
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <algorithm>
#include <memory>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/interpolator.h"
#include "smt-switch/logging_solver.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/solver_factory.h"

using namespace smt;
using smt_tests::ConfigName;
using smt_tests::SolverConfiguration;

namespace {

std::vector<SolverEnum> sorted(std::vector<SolverEnum> enums)
{
  std::sort(enums.begin(), enums.end());
  return enums;
}

TEST(AvailableSolverEnums, ListsTheConfiguredBackends)
{
  EXPECT_EQ(sorted(available_solver_enums()),
            sorted(smt_tests::available_non_generic_solver_enums()));
}

TEST(AvailableInterpolatorEnums, ListsTheConfiguredInterpolators)
{
  EXPECT_EQ(sorted(available_interpolator_enums()),
            sorted(smt_tests::available_interpolator_enums()));
}

TEST(CreateSolverRefusals, GenericSolver)
{
  EXPECT_THROW(create_solver(GENERIC_SOLVER, false), IncorrectUsageException);
}

TEST(CreateSolverRefusals, Interpolator)
{
  EXPECT_THROW(create_solver(CVC5_INTERPOLATOR, false),
               IncorrectUsageException);
}

TEST(CreateInterpolatorRefusals, Solver)
{
  EXPECT_THROW(create_interpolator(CVC5), IncorrectUsageException);
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(CreateSolver);
class CreateSolver : public ::testing::TestWithParam<SolverConfiguration>
{
};

TEST_P(CreateSolver, MakesTheRequestedSolver)
{
  const SolverConfiguration & sc = GetParam();
  SmtSolver s = create_solver(sc.solver_enum, sc.is_logging_solver);
  EXPECT_EQ(s->get_solver_enum(), sc.solver_enum);
  EXPECT_EQ(std::dynamic_pointer_cast<LoggingSolver>(s) != nullptr,
            sc.is_logging_solver);
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(CreateInterpolator);
class CreateInterpolator : public ::testing::TestWithParam<SolverConfiguration>
{
};

TEST_P(CreateInterpolator, MakesTheRequestedInterpolator)
{
  SmtInterpolator itp = create_interpolator(GetParam().solver_enum);
  EXPECT_EQ(itp->get_solver_enum(), GetParam().solver_enum);
}

INSTANTIATE_TEST_SUITE_P(
    SolverFactory,
    CreateSolver,
    testing::ValuesIn(smt_tests::available_non_generic_solver_configurations()),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    SolverFactory,
    CreateInterpolator,
    testing::ValuesIn(smt_tests::available_interpolator_configurations()),
    ConfigName());

}  // namespace
