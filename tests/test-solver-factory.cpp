/*!
 * \file test-solver-factory.cpp
 * \brief Tests creating solvers and interpolators from their kind
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

namespace smt::tests {

namespace {

std::vector<solvers::Kind> sorted(std::vector<solvers::Kind> kinds)
{
  std::sort(kinds.begin(), kinds.end());
  return kinds;
}

bool contains(const std::vector<interpolators::Kind> & kinds,
              interpolators::Kind kind)
{
  return std::find(kinds.begin(), kinds.end(), kind) != kinds.end();
}

TEST(AvailableSolverKinds, ListsTheConfiguredBackends)
{
  std::vector<solvers::Kind> expected;
#ifdef BUILD_BTOR
  expected.push_back(solvers::BTOR);
#endif
#ifdef BUILD_BITWUZLA
  expected.push_back(solvers::BZLA);
#endif
#ifdef BUILD_CVC5
  expected.push_back(solvers::CVC5);
#endif
#ifdef BUILD_MSAT
  expected.push_back(solvers::MSAT);
#endif
#ifdef BUILD_YICES2
  expected.push_back(solvers::YICES2);
#endif
#ifdef BUILD_Z3
  expected.push_back(solvers::Z3);
#endif
  EXPECT_EQ(sorted(solvers::available()), sorted(expected));
}

TEST(AvailableInterpolatorKinds, ListsTheConfiguredInterpolators)
{
  std::vector<interpolators::Kind> available = interpolators::available();
#ifdef SMT_SWITCH_BITWUZLA_HAS_INTERPOLANTS
  EXPECT_TRUE(contains(available, interpolators::BZLA));
#else
  EXPECT_FALSE(contains(available, interpolators::BZLA));
#endif
#ifdef BUILD_CVC5
  EXPECT_TRUE(contains(available, interpolators::CVC5));
#else
  EXPECT_FALSE(contains(available, interpolators::CVC5));
#endif
#ifdef BUILD_MSAT
  EXPECT_TRUE(contains(available, interpolators::MSAT));
#else
  EXPECT_FALSE(contains(available, interpolators::MSAT));
#endif
  // only a Yices2 built with MCSAT interpolates, which only Yices2 can say
  bool yices2_interpolates = true;
  try
  {
    interpolators::create(interpolators::YICES2);
  }
  catch (const NotImplementedException &)
  {
    yices2_interpolates = false;
  }
  EXPECT_EQ(contains(available, interpolators::YICES2), yices2_interpolates);
}

TEST(CreateSolverRefusals, GenericSolver)
{
  EXPECT_THROW(solvers::create(solvers::GENERIC, false),
               IncorrectUsageException);
}

using SolverAndLogging = std::tuple<solvers::Kind, bool>;

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
class CreateSolver : public testing::TestWithParam<SolverAndLogging>
{
};

TEST_P(CreateSolver, MakesTheRequestedSolver)
{
  const auto & [kind, logging] = GetParam();
  SmtSolver s = solvers::create(kind, logging);
  EXPECT_EQ(s->get_kind(), kind);
  EXPECT_EQ(std::dynamic_pointer_cast<LoggingSolver>(s) != nullptr, logging);
}

/** Names a case after its interpolator, e.g. CVC5 */
struct InterpolatorName
{
  std::string operator()(
      const testing::TestParamInfo<interpolators::Kind> & info) const
  {
    return to_string(info.param);
  }
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(CreateInterpolator);
class CreateInterpolator : public testing::TestWithParam<interpolators::Kind>
{
};

TEST_P(CreateInterpolator, MakesTheRequestedInterpolator)
{
  SmtInterpolator itp = interpolators::create(GetParam());
  EXPECT_EQ(itp->get_kind(), GetParam());
}

INSTANTIATE_TEST_SUITE_P(
    SolverFactory,
    CreateSolver,
    testing::Combine(testing::ValuesIn(solvers::available()), testing::Bool()),
    SolverAndLoggingName());

INSTANTIATE_TEST_SUITE_P(SolverFactory,
                         CreateInterpolator,
                         testing::ValuesIn(interpolators::available()),
                         InterpolatorName());

}  // namespace

}  // namespace smt::tests
