/*********************                                                        */
/*! \file unit-term.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for terms.
**
**
**/

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTermTests);
class UnitTermTests : public ::testing::Test,
                      public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  }
  SmtSolver s;
  Sort boolsort, bvsort, funsort, arrsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTermArithTests);
class UnitTermArithTests : public UnitTermTests
{
 protected:
  void SetUp() override
  {
    UnitTermTests::SetUp();
    intsort = s->make_sort(INT);
    realsort = s->make_sort(REAL);
  }
  Sort intsort, realsort;
};

TEST_P(UnitTermTests, FunOp)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  ASSERT_TRUE(x->is_symbol());
  ASSERT_TRUE(x->is_symbolic_const());
  ASSERT_TRUE(f->is_symbol());
  ASSERT_FALSE(f->is_symbolic_const());
}

TEST_P(UnitTermTests, Array)
{
  Term arr = s->make_symbol("arr", arrsort);
  ASSERT_TRUE(arr->is_symbol());
  ASSERT_TRUE(arr->is_symbolic_const());
}

TEST_P(UnitTermArithTests, NegatedValueIsDifferent)
{
  EXPECT_NE(s->make_term(2, intsort), s->make_term(-2, intsort));
  EXPECT_NE(s->make_term(2, realsort), s->make_term(-2, realsort));
}

TEST_P(UnitTermArithTests, MalformedIntStringThrows)
{
  SolverEnum se = s->get_solver_enum();
  if (se == Z3)
  {
    GTEST_SKIP() << "Z3 takes \"\" as an Int and throws z3::exception for "
                    "the others";
  }
  for (const char * val : { "abc", "", "-", "1/2", "1.5" })
  {
    SCOPED_TRACE(val);
    EXPECT_THROW(s->make_term(val, intsort), IncorrectUsageException);
  }
}

TEST_P(UnitTermArithTests, MalformedRealStringThrows)
{
  SolverEnum se = s->get_solver_enum();
  if (se == YICES2)
  {
    GTEST_SKIP() << "Yices2 throws InternalSolverException for them";
  }
  if (se == Z3)
  {
    GTEST_SKIP() << "Z3 takes \"\", \"-\" and \"1.2.3\" as Reals and throws "
                    "z3::exception for the others";
  }
  for (const char * val : { "abc", "", "-", "1/", "1.2.3" })
  {
    SCOPED_TRACE(val);
    EXPECT_THROW(s->make_term(val, realsort), IncorrectUsageException);
  }
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnitTerm,
                         UnitTermTests,
                         testing::ValuesIn(available_solver_configurations()));

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnitTermArith,
                         UnitTermArithTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { THEORY_INT, THEORY_REAL })));

class NegativeValueTests
    : public ::testing::Test,
      public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override { s = create_solver(GetParam()); }
  SmtSolver s;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(NegativeBVTests);
class NegativeBVTests : public NegativeValueTests
{
 protected:
  void SetUp() override
  {
    NegativeValueTests::SetUp();
    bvsort = s->make_sort(BV, 8);
  }
  Sort bvsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(NegativeIntTests);
class NegativeIntTests : public NegativeValueTests
{
 protected:
  void SetUp() override
  {
    NegativeValueTests::SetUp();
    intsort = s->make_sort(INT);
  }
  Sort intsort;
};

TEST_P(NegativeBVTests, IntAndStringAgree)
{
  EXPECT_EQ(s->make_term(-4, bvsort), s->make_term("-4", bvsort));
}

TEST_P(NegativeBVTests, OutOfRangeThrows)
{
  EXPECT_THROW(s->make_term("-129", bvsort), IncorrectUsageException);
}

TEST_P(NegativeBVTests, CancelsItsPositive)
{
  Term sum =
      s->make_term(BVAdd, s->make_term(4, bvsort), s->make_term(-4, bvsort));
  s->assert_formula(
      s->make_term(Not, s->make_term(Equal, sum, s->make_term(0, bvsort))));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST_P(NegativeIntTests, IntAndStringAgree)
{
  EXPECT_EQ(s->make_term(-5, intsort), s->make_term("-5", intsort));
}

TEST_P(NegativeIntTests, CancelsItsPositive)
{
  Term sum =
      s->make_term(Plus, s->make_term(5, intsort), s->make_term(-5, intsort));
  s->assert_formula(
      s->make_term(Not, s->make_term(Equal, sum, s->make_term(0, intsort))));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

INSTANTIATE_TEST_SUITE_P(
    ,
    NegativeBVTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_BV })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ,
    NegativeIntTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_INT })),
    ConfigName());

}  // namespace smt_tests
