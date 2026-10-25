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

#include <cstddef>
#include <functional>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "available_solvers.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace smt_tests;

namespace {

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

  EXPECT_NE(funsort, bvsort);
}

TEST_P(UnitSortTests, SortSet)
{
  UnorderedSortSet sset{
    s->make_sort(BV, 1), s->make_sort(BV, 4), boolsort, s->make_sort(BV, 5)
  };
  // Boolector gives Bool and (_ BitVec 1) one sort, which the logging
  // solver keeps apart
  bool aliased = solver_has_attribute(GetParam().solver_enum, BOOL_BV1_ALIASING)
                 && !GetParam().is_logging_solver;
  EXPECT_EQ(sset.size(), aliased ? 3 : 4);
}

TEST(NullSort, EqualsNullSort)
{
  Sort s1, s2;
  EXPECT_EQ(s1, s2);
  EXPECT_FALSE(s1 != s2);
}

TEST(NullSort, HashesToZero) { EXPECT_EQ(std::hash<Sort>{}(Sort()), 0u); }

TEST(NullSort, PrintsNull)
{
  std::ostringstream out;
  out << Sort();
  EXPECT_EQ(out.str(), "null");
}

TEST_P(UnitSortTests, NullSortDiffersFromSort)
{
  Sort null;
  EXPECT_NE(bvsort, null);
  EXPECT_NE(null, bvsort);
  EXPECT_FALSE(bvsort == null);
  EXPECT_FALSE(null == bvsort);
}

TEST_P(UnitSortTests, NullSortInSet)
{
  UnorderedSortSet sset{ bvsort, Sort(), arrsort, Sort() };
  EXPECT_EQ(sset.size(), 3u);
  EXPECT_EQ(sset.count(Sort()), 1u);
}

TEST_P(UnitSortTests, FunctionSymbolSort)
{
  Term f = s->make_symbol("f", funsort);
  EXPECT_EQ(f->get_sort()->hash(), funsort->hash());
  EXPECT_EQ(f->get_sort(), funsort);
  SortVec domain_sorts = f->get_sort()->get_domain_sorts();
  ASSERT_EQ(domain_sorts.size(), 1);
  EXPECT_EQ(domain_sorts[0], bvsort);
  EXPECT_EQ(f->get_sort()->get_codomain_sort(), bvsort);
}

TEST_P(UnitSortTests, BinaryFunctionSymbolSort)
{
  Sort bv8 = s->make_sort(BV, 8);
  Sort binsort = s->make_sort(FUNCTION, SortVec{ bvsort, bv8, bvsort });
  Term g = s->make_symbol("g", binsort);
  EXPECT_EQ(g->get_sort(), binsort);
  SortVec domain_sorts = g->get_sort()->get_domain_sorts();
  ASSERT_EQ(domain_sorts.size(), 2);
  EXPECT_EQ(domain_sorts[0], bvsort);
  EXPECT_EQ(domain_sorts[1], bv8);
  EXPECT_EQ(g->get_sort()->get_codomain_sort(), bvsort);
}

TEST_P(UnitSortTests, ArrayTermSorts)
{
  Term a = s->make_symbol("a", arrsort);
  Term b = s->make_symbol("b", arrsort);
  Term i = s->make_symbol("i", bvsort);
  Term c = s->make_symbol("c", boolsort);
  for (const Term & t :
       TermVec{ a, s->make_term(Store, a, i, i), s->make_term(Ite, c, a, b) })
  {
    EXPECT_EQ(t->get_sort()->get_sort_kind(), ARRAY) << t;
    EXPECT_EQ(t->get_sort(), arrsort) << t;
  }
}

TEST_P(UnitSortTests, FunctionSortDomainAndCodomain)
{
  // no Bool argument: MathSAT does not take one, so its backend makes it a
  // bit-vector of width one, which the domain then reports
  Sort bvsort8 = s->make_sort(BV, 8);
  Sort binsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort8, bvsort });
  EXPECT_EQ(binsort->get_domain_sorts(), (SortVec{ bvsort, bvsort8 }));
  EXPECT_EQ(binsort->get_codomain_sort(), bvsort);
}

TEST_P(UnitSortTests, FunctionSortArrayDomain)
{
  if (s->get_solver_enum() == BTOR)
  {
    GTEST_SKIP() << "Boolector takes only Bool and bit-vector arguments";
  }
  Sort arrfunsort = s->make_sort(FUNCTION, SortVec{ arrsort, bvsort });
  Sort domain = arrfunsort->get_domain_sorts().at(0);
  EXPECT_EQ(domain, arrsort);
  EXPECT_EQ(domain->get_indexsort(), bvsort);
  EXPECT_EQ(domain->get_elemsort(), bvsort);
}

TEST_P(UnitSortTests, SortParams)
{
  EXPECT_EQ(bvsort->get_width(), 4);
  EXPECT_EQ(arrsort->get_indexsort(), bvsort);
  EXPECT_EQ(arrsort->get_elemsort(), bvsort);
  // not every solver supports querying function types for domain/codomain yet
}

TEST_P(UnitSortTests, SortKinds)
{
  // Boolector gives Bool and (_ BitVec 1) one sort, which the logging
  // solver keeps apart
  bool aliased = solver_has_attribute(GetParam().solver_enum, BOOL_BV1_ALIASING)
                 && !GetParam().is_logging_solver;
  EXPECT_EQ(boolsort->get_sort_kind(), aliased ? BV : BOOL);
  EXPECT_EQ(bvsort->get_sort_kind(), BV);
  EXPECT_EQ(funsort->get_sort_kind(), FUNCTION);
  EXPECT_EQ(arrsort->get_sort_kind(), ARRAY);
}

TEST_P(UnitSortTests, SortVecArgs)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "The generic solver takes the last sort of a FUNCTION "
                    "SortVec as the return sort without checking that any "
                    "remain, so a one-element vector gives a function of no "
                    "arguments instead of throwing";
  }
  Sort arrsort_2 = s->make_sort(ARRAY, SortVec{ bvsort, bvsort });
  EXPECT_EQ(arrsort, arrsort_2);

  EXPECT_THROW(s->make_sort(BV, SortVec{ bvsort }), IncorrectUsageException);
  EXPECT_THROW(s->make_sort(ARRAY, SortVec{ bvsort }), IncorrectUsageException);
  EXPECT_THROW(s->make_sort(ARRAY, SortVec{ bvsort, bvsort, bvsort }),
               IncorrectUsageException);
  EXPECT_THROW(s->make_sort(FUNCTION, SortVec{ bvsort }),
               IncorrectUsageException);
}

TEST_P(UnitSortTests, SortShorthands)
{
  EXPECT_EQ(s->make_sort(FUNCTION, bvsort, boolsort),
            s->make_sort(FUNCTION, SortVec{ bvsort, boolsort }));
  EXPECT_EQ(s->make_sort(FUNCTION, bvsort, bvsort, boolsort),
            s->make_sort(FUNCTION, SortVec{ bvsort, bvsort, boolsort }));
  EXPECT_EQ(
      s->make_sort(FUNCTION, bvsort, bvsort, bvsort, boolsort),
      s->make_sort(FUNCTION, SortVec{ bvsort, bvsort, bvsort, boolsort }));
  EXPECT_THROW(s->make_sort(ARRAY, bvsort), IncorrectUsageException);
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
  EXPECT_EQ(uninterp_sort->get_uninterpreted_name(), "declared-sort");
  EXPECT_EQ(uninterp_sort->get_arity(), 0);
  EXPECT_TRUE(uninterp_sort->get_uninterpreted_param_sorts().empty());

  // Now try non-zero arity (not supported by very many solvers)
  std::size_t num_params = 4;
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
    ASSERT_NE(s->get_solver_enum(), CVC5);
    return;
  }

  ASSERT_TRUE(sort_cons);
  // Expecting an uninterpreted constructor sort
  EXPECT_EQ(sort_cons->get_sort_kind(), UNINTERPRETED_CONS);
  EXPECT_EQ(sort_cons->get_arity(), num_params);

  EXPECT_THROW(s->make_sort(sort_cons, SortVec{ bvsort, bvsort, bvsort }),
               IncorrectUsageException);
  // only a sort constructor can be applied
  EXPECT_THROW(s->make_sort(uninterp_sort, SortVec{ bvsort }),
               IncorrectUsageException);
  EXPECT_THROW(s->make_sort(bvsort, SortVec{ bvsort }),
               IncorrectUsageException);

  Sort param_sort =
      s->make_sort(sort_cons, SortVec{ bvsort, bvsort, bvsort, bvsort });
  SortVec param_sorts = param_sort->get_uninterpreted_param_sorts();
  EXPECT_EQ(param_sorts.size(), num_params);
  EXPECT_EQ(param_sorts[0], bvsort);
  // an applied sort is named after its constructor
  EXPECT_EQ(param_sort->get_sort_kind(), UNINTERPRETED);
  EXPECT_EQ(param_sort->get_uninterpreted_name(), "sort-con");

  // but is identified and printed by its parameters too
  EXPECT_EQ(param_sort,
            s->make_sort(sort_cons, SortVec{ bvsort, bvsort, bvsort, bvsort }));
  EXPECT_NE(param_sort,
            s->make_sort(sort_cons,
                         SortVec{ boolsort, boolsort, boolsort, boolsort }));
  EXPECT_EQ(param_sort->to_string(),
            "(sort-con (_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4))");
  EXPECT_EQ(sort_cons->to_string(), "sort-con");
  EXPECT_EQ(sort_cons, sort_cons);
}

TEST_P(UnitSortTests, ArityOnlyForUninterpretedSorts)
{
  for (const Sort & sort : SortVec{ boolsort, bvsort, funsort, arrsort })
  {
    EXPECT_THAT([&] { sort->get_arity(); },
                testing::ThrowsMessage<IncorrectUsageException>(testing::StrEq(
                    "Sort of kind " + to_string(sort->get_sort_kind())
                    + " has no arity")))
        << sort;
  }
}

TEST_P(UnitSortTests, UninterpretedNameOnlyForUninterpretedSorts)
{
  for (const Sort & sort : SortVec{ boolsort, bvsort, funsort, arrsort })
  {
    EXPECT_THAT([&] { sort->get_uninterpreted_name(); },
                testing::ThrowsMessage<IncorrectUsageException>(testing::StrEq(
                    "Sort of kind " + to_string(sort->get_sort_kind())
                    + " has no uninterpreted name")))
        << sort;
  }
}

TEST_P(UnitSortTests, AccessorsOnlyForTheirKinds)
{
  struct Accessor
  {
    std::string missing;
    std::unordered_set<SortKind> kinds;
    std::function<void(const Sort &)> call;
  };
  const std::vector<Accessor> accessors{
    { "width", { BV }, [](const Sort & sort) { sort->get_width(); } },
    { "index sort",
      { ARRAY },
      [](const Sort & sort) { sort->get_indexsort(); } },
    { "element sort",
      { ARRAY },
      [](const Sort & sort) { sort->get_elemsort(); } },
    { "domain sorts",
      { FUNCTION },
      [](const Sort & sort) { sort->get_domain_sorts(); } },
    { "codomain sort",
      { FUNCTION },
      [](const Sort & sort) { sort->get_codomain_sort(); } },
    { "uninterpreted param sorts",
      { UNINTERPRETED },
      [](const Sort & sort) { sort->get_uninterpreted_param_sorts(); } },
    { "datatype",
      { DATATYPE },
      [](const Sort & sort) { sort->get_datatype(); } },
  };
  for (const Sort & sort : SortVec{ boolsort, bvsort, funsort, arrsort })
  {
    SortKind sk = sort->get_sort_kind();
    for (const Accessor & accessor : accessors)
    {
      if (accessor.kinds.count(sk))
      {
        continue;
      }
      EXPECT_THAT(
          [&] { accessor.call(sort); },
          testing::ThrowsMessage<IncorrectUsageException>(testing::StrEq(
              "Sort of kind " + to_string(sk) + " has no " + accessor.missing)))
          << sort;
    }
  }
}

TEST_P(UnitSortTests, UninterpSortEquality)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "The generic solver cannot get the value of a term whose "
                    "sort kind is Uninterpreted";
  }

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
  s->assert_formula(s->make_term(Equal, x, y));
  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  Term xv = s->get_value(x);
  Term yv = s->get_value(y);
  s->pop();

  ASSERT_EQ(xv, yv);

  Term xeq = s->make_term(Equal, x, xv);
  Term yeq = s->make_term(Equal, y, yv);

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

TEST_P(UnitSortArithTests, SortKinds)
{
  EXPECT_EQ(intsort->get_sort_kind(), INT);
  EXPECT_EQ(realsort->get_sort_kind(), REAL);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSortTests,
                         UnitSortTests,
                         testing::ValuesIn(available_solver_configurations()));

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSortArithTests,
                         UnitSortArithTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { THEORY_INT, THEORY_REAL })));

}  // namespace
