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
#include <unordered_set>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/solver_factory.h"

namespace smt::tests {

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSolverEnumTests);
class UnitSolverEnumTests
    : public testing::Test,
      public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override { s = create_solver(GetParam()); }
  SmtSolver s;
};

TEST_P(UnitSolverEnumTests, SolverEnumMatch)
{
  SolverConfiguration sc = GetParam();
  SolverEnum se = sc.solver_enum;
  ASSERT_EQ(se, s->get_solver_enum());
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedUnitSolverEnum,
    UnitSolverEnumTests,
    testing::ValuesIn(available_solver_configurations_with_generic()));

TEST(UnitSolverEnumNames, EverySolverEnumPrints)
{
  const std::vector<std::pair<SolverEnum, std::string>> names({
      { BTOR, "BTOR" },
      { BZLA, "BZLA" },
      { CVC5, "CVC5" },
      { GENERIC_SOLVER, "GENERIC_SOLVER" },
      { MSAT, "MSAT" },
      { YICES2, "YICES2" },
      { Z3, "Z3" },
      { BZLA_INTERPOLATOR, "BZLA_INTERPOLATOR" },
      { CVC5_INTERPOLATOR, "CVC5_INTERPOLATOR" },
      { MSAT_INTERPOLATOR, "MSAT_INTERPOLATOR" },
      { YICES2_INTERPOLATOR, "YICES2_INTERPOLATOR" },
  });
  for (const auto & [se, name] : names)
  {
    EXPECT_EQ(to_string(se), name);
  }
}

TEST(UnitSolverAttributes, FullTransferIsTermIterWithoutAliasing)
{
  // a backend that breaks this has to say so here, rather than let the
  // attributes drift apart
  for (SolverEnum se : solvers::available())
  {
    EXPECT_EQ(
        solver_has_attribute(se, SolverAttribute::FULL_TRANSFER),
        solver_has_attribute(se, SolverAttribute::TERMITER)
            && !solver_has_attribute(se, SolverAttribute::BOOL_BV1_ALIASING))
        << to_string(se);
  }
  // TermTranslator refuses the generic solver whatever it iterates
  EXPECT_FALSE(
      solver_has_attribute(GENERIC_SOLVER, SolverAttribute::FULL_TRANSFER));
}

TEST(UnitSolverAttributes, InterpolatorsShareTheirSolversAttributes)
{
  for (SolverEnum se :
       { BZLA_INTERPOLATOR, CVC5_INTERPOLATOR, MSAT_INTERPOLATOR })
  {
    EXPECT_EQ(get_solver_attributes(se),
              get_solver_attributes(interpolator_base_solver(se)))
        << to_string(se);
  }
}

}  // namespace

}  // namespace smt::tests
