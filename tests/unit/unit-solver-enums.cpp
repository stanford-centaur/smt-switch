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

#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSolverEnumTests);
class UnitSolverEnumTests : public ::testing::Test,
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

}  // namespace smt_tests
