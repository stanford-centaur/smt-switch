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

class UnitSolverEnumTests : public ::testing::Test,
                            public ::testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override { s = create_solver(GetParam()); }
  SmtSolver s;
};

TEST_P(UnitSolverEnumTests, SolverEnumMatch)
{
  ASSERT_EQ(GetParam(), s->get_solver_enum());
}

TEST_P(UnitSolverEnumTests, LoggingMapping)
{
  SolverEnum se = GetParam();
  if (!is_logging(se))
  {
    ASSERT_NO_THROW(get_logging_solver_enum(se));
  }
  else
  {
    ASSERT_THROW(get_logging_solver_enum(se), IncorrectUsageException);
  }
}

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSolverEnum,
                         UnitSolverEnumTests,
                         testing::ValuesIn(available_solver_enums()));

}  // namespace smt_tests
