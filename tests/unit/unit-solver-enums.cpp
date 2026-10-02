/*********************                                                        */
/*! \file unit-solver-enums.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for theory of arrays.
**
**
**/

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSolverEnumTests);
class UnitSolverEnumTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
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

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSolverEnum,
                         UnitSolverEnumTests,
                         testing::ValuesIn(available_solver_configurations()));

TEST(UnitSolverEnumNames, EverySolverEnumPrints)
{
  const vector<pair<SolverEnum, string>> names({
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
  });
  for (const auto & [se, name] : names)
  {
    EXPECT_EQ(to_string(se), name);
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

}  // namespace smt_tests
