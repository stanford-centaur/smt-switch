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

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSolverEnumTests);
class UnitSolverEnumTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override { s = create_solver(GetParam()); }
  SmtSolver s;
};

TEST_P(UnitSolverEnumTests, SolverKindMatch)
{
  EXPECT_EQ(GetParam().solver_kind, s->get_kind());
}

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSolverEnum,
                         UnitSolverEnumTests,
                         testing::ValuesIn(available_solver_configurations()));

TEST(UnitSolverEnumNames, EverySolverKindPrints)
{
  const vector<pair<SolverKind, string>> names({
      { SolverKind::BTOR, "BTOR" },
      { SolverKind::BZLA, "BZLA" },
      { SolverKind::CVC5, "CVC5" },
      { SolverKind::GENERIC, "GENERIC" },
      { SolverKind::MSAT, "MSAT" },
      { SolverKind::YICES2, "YICES2" },
      { SolverKind::Z3, "Z3" },
  });
  for (const auto & [solver_kind, name] : names)
  {
    EXPECT_EQ(to_string(solver_kind), name);
  }
}

TEST(UnitSolverEnumNames, EveryInterpolatorKindPrints)
{
  const vector<pair<InterpolatorKind, string>> names({
      { InterpolatorKind::BZLA, "BZLA" },
      { InterpolatorKind::CVC5, "CVC5" },
      { InterpolatorKind::MSAT, "MSAT" },
      { InterpolatorKind::YICES2, "YICES2" },
  });
  for (const auto & [itp_kind, name] : names)
  {
    EXPECT_EQ(to_string(itp_kind), name);
  }
}

TEST(UnitSolverEnumNames, EverySolverAttributePrints)
{
  const vector<pair<SolverAttribute, string>> names({
      { LOGGING, "LOGGING" },
      { TERMITER, "TERMITER" },
      { THEORY_BV, "THEORY_BV" },
      { THEORY_INT, "THEORY_INT" },
      { THEORY_REAL, "THEORY_REAL" },
      { THEORY_STR, "THEORY_STR" },
      { ARRAY_MODELS, "ARRAY_MODELS" },
      { CONSTARR, "CONSTARR" },
      { FULL_TRANSFER, "FULL_TRANSFER" },
      { ARRAY_FUN_BOOLS, "ARRAY_FUN_BOOLS" },
      { UNSAT_CORE, "UNSAT_CORE" },
      { THEORY_DATATYPE, "THEORY_DATATYPE" },
      { QUANTIFIERS, "QUANTIFIERS" },
      { UNINTERP_SORT, "UNINTERP_SORT" },
      { PARAM_UNINTERP_SORT, "PARAM_UNINTERP_SORT" },
      { BOOL_BV1_ALIASING, "BOOL_BV1_ALIASING" },
      { TIMELIMIT, "TIMELIMIT" },
  });
  for (const auto & [sa, name] : names)
  {
    EXPECT_EQ(to_string(sa), name);
  }
}

TEST(UnitSolverAttributes, FullTransferIsTermIterWithoutAliasing)
{
  // a backend that breaks this has to say so here, rather than let the
  // attributes drift apart
  for (SolverKind solver_kind : available_non_generic_solver_kinds())
  {
    EXPECT_EQ(solver_has_attribute(solver_kind, FULL_TRANSFER),
              solver_has_attribute(solver_kind, TERMITER)
                  && !solver_has_attribute(solver_kind, BOOL_BV1_ALIASING))
        << to_string(solver_kind);
  }
  // TermTranslator refuses the generic solver whatever it iterates
  EXPECT_FALSE(solver_has_attribute(SolverKind::GENERIC, FULL_TRANSFER));
}

TEST(UnitSolverAttributes, InterpolatorsBuildTermsWithTheirOwnBackend)
{
  for (InterpolatorKind itp_kind : { InterpolatorKind::BZLA,
                                     InterpolatorKind::CVC5,
                                     InterpolatorKind::MSAT,
                                     InterpolatorKind::YICES2 })
  {
    EXPECT_EQ(to_string(solver_kind(itp_kind)), to_string(itp_kind));
  }
}

}  // namespace
