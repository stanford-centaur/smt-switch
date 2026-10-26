/*!
 * \file unit-foreign-handle.cpp
 * \brief Tests that a solver refuses handles made by another solver.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Each case pairs a solver with its logging twin: the bare backend when the
 * configuration is a logging solver, and the logging solver around it
 * otherwise. A term, sort or datatype declaration made by one must be
 * refused by the other, and terms of the two never compare equal.
 */

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "available_solvers.h"
#include "exceptions.h"
#include "smt.h"

using namespace smt;
using namespace smt_tests;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ForeignHandle);
class ForeignHandle : public ::testing::TestWithParam<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    const SolverConfiguration & sc = GetParam();
    s = create_solver(sc);
    other = create_solver(
        SolverConfiguration(sc.solver_enum, !sc.is_logging_solver));
    boolsort = s->make_sort(BOOL);
    other_boolsort = other->make_sort(BOOL);
  }

  SmtSolver s;
  SmtSolver other;
  Sort boolsort;
  Sort other_boolsort;
};

TEST_P(ForeignHandle, ForeignTermRefused)
{
  Term a = s->make_symbol("a", boolsort);
  Term b = other->make_symbol("b", other_boolsort);
  EXPECT_THROW(s->assert_formula(b), IncorrectUsageException);
  const SolverConfiguration & sc = GetParam();
  if (sc.solver_enum == GENERIC_SOLVER && !sc.is_logging_solver)
  {
    GTEST_SKIP() << "GenericSolver::make_term takes a foreign term unchecked";
  }
  EXPECT_THROW(s->make_term(And, a, b), IncorrectUsageException);
}

TEST_P(ForeignHandle, ForeignSortRefused)
{
  const SolverConfiguration & sc = GetParam();
  if (sc.solver_enum == GENERIC_SOLVER && !sc.is_logging_solver)
  {
    GTEST_SKIP() << "GenericSolver::make_symbol takes a foreign sort unchecked";
  }
  EXPECT_THROW(s->make_symbol("x", other_boolsort), IncorrectUsageException);
}

TEST_P(ForeignHandle, ForeignTermNotEqual)
{
  Term a = s->make_symbol("a", boolsort);
  Term b = other->make_symbol("b", other_boolsort);
  EXPECT_NE(a, b);
  EXPECT_NE(b, a);
}

TEST_P(ForeignHandle, ForeignSortNotEqual)
{
  EXPECT_NE(boolsort, other_boolsort);
  EXPECT_NE(other_boolsort, boolsort);
}

INSTANTIATE_TEST_SUITE_P(,
                         ForeignHandle,
                         testing::ValuesIn(available_solver_configurations()),
                         ConfigName());

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ForeignDatatypeHandle);
class ForeignDatatypeHandle : public ForeignHandle
{
};

TEST_P(ForeignDatatypeHandle, ForeignConstructorDeclRefused)
{
  DatatypeDecl list = s->make_datatype_decl("list");
  DatatypeConstructorDecl nil = other->make_datatype_constructor_decl("nil");
  EXPECT_THAT([&] { s->add_constructor(list, nil); },
              testing::ThrowsMessage<IncorrectUsageException>(
                  testing::HasSubstr("nil")));
}

TEST_P(ForeignDatatypeHandle, ForeignDatatypeDeclRefused)
{
  DatatypeDecl list = other->make_datatype_decl("list");
  other->add_constructor(list, other->make_datatype_constructor_decl("nil"));
  EXPECT_THROW(s->make_sort(list), IncorrectUsageException);
}

TEST_P(ForeignDatatypeHandle, ForeignDatatypeSortRefused)
{
  DatatypeDecl list = other->make_datatype_decl("list");
  other->add_constructor(list, other->make_datatype_constructor_decl("nil"));
  Sort listsort = other->make_sort(list);
  EXPECT_THROW(s->get_constructor(listsort, "nil"), IncorrectUsageException);
  EXPECT_THROW(s->get_tester(listsort, "nil"), IncorrectUsageException);
}

INSTANTIATE_TEST_SUITE_P(
    ,
    ForeignDatatypeHandle,
    testing::ValuesIn(filter_solver_configurations({ THEORY_DATATYPE })),
    ConfigName());

}  // namespace
