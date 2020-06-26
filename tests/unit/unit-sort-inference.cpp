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
  EXPECT_TRUE(is_sort_equal({ boolsort, boolsort }));
  EXPECT_TRUE(is_sort_equal({ bvsort4, bvsort4 }));
  EXPECT_TRUE(is_sort_equal({ arrsort, arrsort }));
  EXPECT_TRUE(is_sort_equal({ funsort, funsort }));
  EXPECT_FALSE(is_sort_equal({ boolsort, bvsort4 }));
  EXPECT_FALSE(is_sort_equal({ bvsort4, bvsort5 }));
  EXPECT_TRUE(is_sortkind_equal({ bvsort4, bvsort5 }));
}

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSortInference,
                         UnitSortInferenceTests,
                         testing::ValuesIn(available_solver_enums()));

}  // namespace smt_tests
