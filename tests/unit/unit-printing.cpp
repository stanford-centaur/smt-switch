/*********************                                                        */
/*! \file unit-printing.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for printing
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitPrintTests);
class UnitPrintTests : public ::testing::Test,
                       public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    boolsort = s->make_sort(BOOL);
    bvsort1 = s->make_sort(BV, 1);
    bvsort4 = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort4, bvsort4 });
  }
  SmtSolver s;
  Sort boolsort, bvsort1, bvsort4, funsort;
};

TEST_P(UnitPrintTests, SortKind)
{
  ASSERT_EQ(smt::to_string(ARRAY), "Array");
  ASSERT_EQ(smt::to_string(BOOL), "Bool");
  ASSERT_EQ(smt::to_string(BV), "BitVec");
  ASSERT_EQ(smt::to_string(INT), "Int");
  ASSERT_EQ(smt::to_string(REAL), "Real");
  ASSERT_EQ(smt::to_string(FUNCTION), "Function");
}

TEST_P(UnitPrintTests, Sort)
{
  ASSERT_EQ(bvsort4->to_string(), "(_ BitVec 4)");
}

TEST_P(UnitPrintTests, Result)
{
  Result sat(SAT);
  Result unsat(UNSAT);
  Result unknown(UNKNOWN);
  ASSERT_EQ(sat.to_string(), "sat");
  ASSERT_EQ(unsat.to_string(), "unsat");
  ASSERT_EQ(unknown.to_string(), "unknown");
}

TEST_P(UnitPrintTests, Op)
{
  ASSERT_EQ(smt::to_string(BVAdd), "bvadd");
  ASSERT_EQ(smt::to_string(Implies), "=>");
  ASSERT_EQ(smt::to_string(Plus), "+");
  ASSERT_EQ(Op(Extract, 4, 0).to_string(), "(_ extract 4 0)");
}

TEST_P(UnitPrintTests, PrintValueAs)
{
  // Test the helper function that is used in the LoggingTerm for printing
  // values
  Term t = s->make_term(true);
  Term f = s->make_term(false);
  Term bv1 = s->make_term(1, bvsort1);
  Term bv0 = s->make_term(0, bvsort1);
  Term x = s->make_symbol("x", bvsort1);
  ASSERT_EQ(t->print_value_as(BOOL), "true");
  ASSERT_EQ(f->print_value_as(BOOL), "false");
  std::string bv1_repr = bv1->print_value_as(BV);
  std::string bv0_repr = bv0->print_value_as(BV);
  ASSERT_TRUE(bv1_repr == "#b1" || bv1_repr == "(_ bv1 1)");
  ASSERT_TRUE(bv0_repr == "#b0" || bv0_repr == "(_ bv0 1)");
  ASSERT_THROW(x->print_value_as(BV), IncorrectUsageException);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverPringUnit,
                         UnitPrintTests,
                         testing::ValuesIn(available_solver_configurations()));

}  // namespace smt_tests
