/*********************                                                        */
/*! \file unit-sort-inference.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for sort inference
**
**
**/

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"
#include "sort_inference.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class UnitSortInferenceTests : public ::testing::Test,
                               public ::testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");

    boolsort = s->make_sort(BOOL);
    bvsort4 = s->make_sort(BV, 4);
    bvsort5 = s->make_sort(BV, 5);
    arrsort = s->make_sort(ARRAY, bvsort4, bvsort4);
    funsort = s->make_sort(FUNCTION, { bvsort4, bvsort4, boolsort });
  }
  SmtSolver s;
  Sort boolsort, bvsort4, bvsort5, arrsort, funsort;
};

TEST_P(UnitSortInferenceTests, HelperTests)
{
  EXPECT_TRUE(equal_sorts({ boolsort, boolsort }));
  EXPECT_TRUE(equal_sorts({ bvsort4, bvsort4 }));
  EXPECT_TRUE(equal_sorts({ arrsort, arrsort }));
  EXPECT_TRUE(equal_sorts({ funsort, funsort }));
  EXPECT_FALSE(equal_sorts({ boolsort, bvsort4 }));
  EXPECT_FALSE(equal_sorts({ bvsort4, bvsort5 }));

  EXPECT_TRUE(equal_sortkinds({ bvsort4, bvsort5 }));
  EXPECT_TRUE(equal_sortkinds({ funsort, funsort }));
  EXPECT_FALSE(equal_sortkinds({ funsort, bvsort4 }));

  EXPECT_FALSE(check_ite_sorts({ boolsort, bvsort4, bvsort5 }));

  // BTOR considers all BOOLs as BV of size 1, so these tests would fail
  if (s->get_solver_enum() != BTOR)
  {
    EXPECT_TRUE(check_ite_sorts({ boolsort, bvsort4, bvsort4 }));
    EXPECT_TRUE(bool_sorts({ boolsort }));
  }

  EXPECT_TRUE(bv_sorts({ bvsort4 }));
  EXPECT_TRUE(array_sorts({ arrsort }));
  EXPECT_TRUE(function_sorts({ funsort }));
}

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSortInference,
                         UnitSortInferenceTests,
                         testing::ValuesIn(available_solver_enums()));

}  // namespace smt_tests
