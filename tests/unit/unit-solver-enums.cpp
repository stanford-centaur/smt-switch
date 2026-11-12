/*!
 * \file unit-solver-enums.cpp
 * \brief Unit tests for theory of arrays
 * \author Makai Mann
 * \author Áron Ricardo Perez-Lopez
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <string>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/solver_factory.h"

namespace smt::tests {

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSolverKindTests);
class UnitSolverKindTests
    : public testing::Test,
      public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override { s = create_solver(GetParam()); }
  SmtSolver s;
};

TEST_P(UnitSolverKindTests, SolverKindMatch)
{
  EXPECT_EQ(s->get_kind(), GetParam().solver_kind);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedUnitSolverKind,
    UnitSolverKindTests,
    testing::ValuesIn(available_solver_configurations_with_generic()));

TEST(UnitSolverKindNames, EverySolverKindPrints)
{
  const std::vector<std::pair<solvers::Kind, std::string>> names({
      { solvers::BTOR, "BTOR" },
      { solvers::BZLA, "BZLA" },
      { solvers::CVC5, "CVC5" },
      { solvers::GENERIC, "GENERIC" },
      { solvers::MSAT, "MSAT" },
      { solvers::YICES2, "YICES2" },
      { solvers::Z3, "Z3" },
  });
  for (const auto & [kind, name] : names)
  {
    EXPECT_EQ(to_string(kind), name);
  }
}

TEST(UnitSolverKindNames, EveryInterpolatorKindPrintsAsItsSolver)
{
  const std::vector<std::pair<interpolators::Kind, solvers::Kind>> kinds({
      { interpolators::BZLA, solvers::BZLA },
      { interpolators::CVC5, solvers::CVC5 },
      { interpolators::MSAT, solvers::MSAT },
      { interpolators::YICES2, solvers::YICES2 },
  });
  for (const auto & [itp_kind, solver_kind] : kinds)
  {
    EXPECT_EQ(interpolators::solver_kind(itp_kind), solver_kind);
    EXPECT_EQ(to_string(itp_kind), to_string(solver_kind));
  }
}

TEST(UnitSolverAttributes, FullTransferIsTermIterWithoutAliasing)
{
  // a backend that breaks this has to say so here, rather than let the
  // attributes drift apart
  for (solvers::Kind kind : solvers::available())
  {
    EXPECT_EQ(
        solver_has_attribute(kind, SolverAttribute::FULL_TRANSFER),
        solver_has_attribute(kind, SolverAttribute::TERMITER)
            && !solver_has_attribute(kind, SolverAttribute::BOOL_BV1_ALIASING))
        << to_string(kind);
  }
  // TermTranslator refuses the generic solver whatever it iterates
  EXPECT_FALSE(
      solver_has_attribute(solvers::GENERIC, SolverAttribute::FULL_TRANSFER));
}

}  // namespace

}  // namespace smt::tests
