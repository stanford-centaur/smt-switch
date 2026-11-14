/*!
 * \file test-solver-factory.cpp
 * \brief Tests creating solvers and interpolators from their solver enum
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * With a shared libsmt-switch this program links no backend, so every
 * backend it reaches is one create_solver loaded.
 */
#include <gtest/gtest.h>

#include <algorithm>
#include <memory>
#include <string>
#include <tuple>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/interpolator.h"
#include "smt-switch/logging_solver.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/solver_factory.h"

using namespace smt;

namespace {

std::vector<SolverEnum> sorted(std::vector<SolverEnum> enums)
{
  std::sort(enums.begin(), enums.end());
  return enums;
}

bool contains(const std::vector<SolverEnum> & enums, SolverEnum se)
{
  return std::find(enums.begin(), enums.end(), se) != enums.end();
}

TEST(AvailableSolverEnums, ListsTheConfiguredBackends)
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
  EXPECT_EQ(sorted(available_solver_enums()), sorted(expected));
}

TEST(AvailableInterpolatorEnums, ListsTheConfiguredInterpolators)
{
  std::vector<SolverEnum> available = available_interpolator_enums();
#ifdef SMT_SWITCH_BITWUZLA_HAS_INTERPOLANTS
  EXPECT_TRUE(contains(available, BZLA_INTERPOLATOR));
#else
  EXPECT_FALSE(contains(available, BZLA_INTERPOLATOR));
#endif
#ifdef BUILD_CVC5
  EXPECT_TRUE(contains(available, CVC5_INTERPOLATOR));
#else
  EXPECT_FALSE(contains(available, CVC5_INTERPOLATOR));
#endif
#ifdef BUILD_MSAT
  EXPECT_TRUE(contains(available, MSAT_INTERPOLATOR));
#else
  EXPECT_FALSE(contains(available, MSAT_INTERPOLATOR));
#endif
  // only a Yices2 built with MCSAT interpolates, which only Yices2 can say
  bool yices2_interpolates = true;
  try
  {
    create_interpolator(YICES2_INTERPOLATOR);
  }
  catch (const NotImplementedException &)
  {
    yices2_interpolates = false;
  }
  EXPECT_EQ(contains(available, YICES2_INTERPOLATOR), yices2_interpolates);
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

using SolverAndLogging = std::tuple<SolverEnum, bool>;

/** Names a case after its solver and whether it logs, e.g. CVC5_LOGGING */
struct SolverAndLoggingName
{
  std::string operator()(
      const testing::TestParamInfo<SolverAndLogging> & info) const
  {
    std::string name = to_string(std::get<0>(info.param));
    if (std::get<1>(info.param))
    {
      name += "_LOGGING";
    }
    return name;
  }
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(CreateSolver);
class CreateSolver : public ::testing::TestWithParam<SolverAndLogging>
{
};

TEST_P(CreateSolver, MakesTheRequestedSolver)
{
  const auto & [se, logging] = GetParam();
  SmtSolver s = create_solver(se, logging);
  EXPECT_EQ(s->get_solver_enum(), se);
  EXPECT_EQ(std::dynamic_pointer_cast<LoggingSolver>(s) != nullptr, logging);
}

/** Names a case after its interpolator, e.g. CVC5_INTERPOLATOR */
struct InterpolatorName
{
  std::string operator()(const testing::TestParamInfo<SolverEnum> & info) const
  {
    return to_string(info.param);
  }
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(CreateInterpolator);
class CreateInterpolator : public ::testing::TestWithParam<SolverEnum>
{
};

TEST_P(CreateInterpolator, MakesTheRequestedInterpolator)
{
  SmtInterpolator itp = create_interpolator(GetParam());
  EXPECT_EQ(itp->get_solver_enum(), GetParam());
}

INSTANTIATE_TEST_SUITE_P(
    SolverFactory,
    CreateSolver,
    testing::Combine(testing::ValuesIn(available_solver_enums()),
                     testing::Bool()),
    SolverAndLoggingName());

INSTANTIATE_TEST_SUITE_P(SolverFactory,
                         CreateInterpolator,
                         testing::ValuesIn(available_interpolator_enums()),
                         InterpolatorName());

}  // namespace
