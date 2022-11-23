/*********************                                           */
/*! \file unit-sort.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for sorts
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSortTests);
class UnitSortTests : public ::testing::Test,
                      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    s->set_opt("incremental", "true");

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  }
  SmtSolver s;
  Sort boolsort, bvsort, funsort, arrsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSortArithTests);
class UnitSortArithTests : public UnitSortTests
{
 protected:
  void SetUp() override
  {
    UnitSortTests::SetUp();
    intsort = s->make_sort(INT);
    realsort = s->make_sort(REAL);
  }
  Sort intsort, realsort;
};

TEST_P(UnitSortTests, SameSortDiffObj)
{
  Sort boolsort_2 = s->make_sort(BOOL);
  EXPECT_EQ(boolsort->hash(), boolsort_2->hash());
  EXPECT_EQ(boolsort, boolsort_2);

  Sort bvsort_2 = s->make_sort(BV, 4);
  EXPECT_EQ(bvsort->hash(), bvsort_2->hash());
  EXPECT_EQ(bvsort, bvsort_2);

  Sort bvsort8 = s->make_sort(BV, 8);
  EXPECT_NE(bvsort, bvsort8);

  Sort funsort_2 = s->make_sort(FUNCTION, { bvsort, bvsort_2 });
  EXPECT_EQ(funsort->hash(), funsort_2->hash());
  EXPECT_EQ(funsort, funsort_2);

  Sort arrsort_2 = s->make_sort(ARRAY, bvsort, bvsort_2);
  EXPECT_EQ(arrsort->hash(), arrsort_2->hash());
  EXPECT_EQ(arrsort, arrsort_2);
}

TEST_P(UnitSortTests, SortParams)
{
  EXPECT_EQ(bvsort->get_width(), 4);
  EXPECT_EQ(arrsort->get_indexsort(), bvsort);
  EXPECT_EQ(arrsort->get_elemsort(), bvsort);
  // not every solver supports querying function types for domain/codomain yet
}

TEST_P(UnitSortTests, UninterpretedSort)
{
  Sort uninterp_sort;
  try
  {
    uninterp_sort = s->make_sort("declared-sort", 0);
  }
  catch (SmtException & e)
  {
    // if not supported, that's fine.
    std::cout << "got exception when declaring sort: " << e.what() << std::endl;
    return;
  }

  ASSERT_TRUE(uninterp_sort);
  EXPECT_EQ(uninterp_sort->get_sort_kind(), UNINTERPRETED);
  EXPECT_EQ(uninterp_sort->get_arity(), 0);

  // Now try non-zero arity (not supported by very many solvers)
  size_t num_params = 4;
  Sort sort_cons;
  try
  {
    sort_cons = s->make_sort("sort-con", num_params);
  }
  catch (SmtException & e)
  {
    // if not supported, that's fine.
    std::cout << "got exception when declaring nonzero arity sort: " << e.what()
              << std::endl;
    // but CVC5 expected to support it
    ASSERT_NE(s->get_solver_enum(), smt::CVC5);
    return;
  }

  ASSERT_TRUE(sort_cons);
  // Expecting an uninterpreted constructor sort
  EXPECT_EQ(sort_cons->get_sort_kind(), UNINTERPRETED_CONS);
  EXPECT_EQ(sort_cons->get_arity(), num_params);

  EXPECT_THROW(s->make_sort(sort_cons, SortVec{ bvsort, bvsort, bvsort }),
               IncorrectUsageException);

  Sort param_sort =
      s->make_sort(sort_cons, SortVec{ bvsort, bvsort, bvsort, bvsort });
  SortVec param_sorts = param_sort->get_uninterpreted_param_sorts();
  EXPECT_EQ(param_sorts.size(), num_params);
  EXPECT_EQ(param_sorts[0], bvsort);
}

TEST_P(UnitSortTests, UninterpSortEquality)
{
  if (GetParam().is_logging_solver)
  {
    // need some additional fixes for is_value in LoggingSolver to handle
    // uninterpreted sorts
    return;
  }

  Sort uninterp_sort;
  try
  {
    uninterp_sort = s->make_sort("uninterp-sort", 0);
  }
  catch (SmtException & e)
  {
    SolverConfiguration sc = GetParam();
    SolverEnum se = sc.solver_enum;
    std::cout << "got exception for SolverEnum: " << se << std::endl;
    return;
  }

  Term x = s->make_symbol("x", uninterp_sort);
  Term y = s->make_symbol("y", uninterp_sort);
  ASSERT_EQ(x->get_sort(), uninterp_sort);
  ASSERT_EQ(x->get_sort(), y->get_sort());

  s->push();
  s->make_term(Equal, x, y);
  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  Term xv = s->get_value(x);
  Term yv = s->get_value(y);
  s->pop();

  ASSERT_EQ(xv, yv);

  Term xeq = s->make_term(Equal, x, xv);
  Term yeq = s->make_term(Equal, y, yv);

  std::cout << "xeq: " << xeq << std::endl;
  std::cout << "yeq: " << yeq << std::endl;

  s->assert_formula(s->make_term(Distinct, x, y));
  s->assert_formula(xeq);
  s->assert_formula(yeq);
  r = s->check_sat();
  ASSERT_TRUE(r.is_unsat());
}

TEST_P(UnitSortArithTests, SameSortDiffObj)
{
  Sort intsort_2 = s->make_sort(INT);
  EXPECT_EQ(intsort->hash(), intsort_2->hash());
  EXPECT_EQ(intsort, intsort_2);

  Sort realsort_2 = s->make_sort(REAL);
  EXPECT_EQ(realsort->hash(), realsort_2->hash());
  EXPECT_EQ(realsort, realsort_2);
}

// One of the tests requries parsing values
// of uninterpreted sorts.
// This is not supported by the generic solver, and hence
// it is excluded.
INSTANTIATE_TEST_SUITE_P(
    ParameterizedUnitSortTests,
    UnitSortTests,
    testing::ValuesIn(available_non_generic_solver_configurations()));

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSortArithTests,
                         UnitSortArithTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { THEORY_INT, THEORY_REAL })));

}  // namespace smt_tests
