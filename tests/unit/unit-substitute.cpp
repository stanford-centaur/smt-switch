/*!
 * \file unit-substitute.cpp
 * \brief Unit tests for term substitution
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <memory>
#include <string>
#include <unordered_set>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/substitution_walker.h"
#include "smt-switch/term.h"
#include "smt-switch/utils.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSubstituteTests);
class UnitSubstituteTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    bvsort = s->make_sort(BV, 4);
    x = s->make_symbol("x", bvsort);
    y = s->make_symbol("y", bvsort);
    xpy = s->make_term(BVAdd, x, y);

    a = s->make_symbol("a", bvsort);
    b = s->make_symbol("b", bvsort);
  }
  SmtSolver s;
  Sort bvsort;
  Term x, y, xpy, a, b;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSubstituteIterTests);
class UnitSubstituteIterTests : public UnitSubstituteTests
{
};

TEST_P(UnitSubstituteTests, CheckSubstitution1)
{
  UnorderedTermMap subs_map({ { x, a }, { y, b } });
  Term apb = s->substitute(xpy, subs_map);
  Term apb_expect = s->make_term(BVAdd, a, b);
  EXPECT_EQ(apb, apb_expect);
}

TEST_P(UnitSubstituteTests, CheckSubstitution2)
{
  UnorderedTermMap subs_map({ { x, a } });
  Term apy = s->substitute(xpy, subs_map);
  Term apy_expect = s->make_term(BVAdd, a, y);
  EXPECT_EQ(apy, apy_expect);
}

TEST_P(UnitSubstituteTests, EmptySubstitution)
{
  EXPECT_EQ(s->substitute(xpy, UnorderedTermMap{}), xpy);
}

TEST_P(UnitSubstituteTests, CheckSubstitution3)
{
  Term apb = s->make_term(BVAdd, a, b);
  UnorderedTermMap subs_map({ { x, xpy }, { y, apb } });
  Term result = s->substitute(xpy, subs_map);
  Term expect = s->make_term(BVAdd, xpy, apb);
  EXPECT_EQ(result, expect);
}

TEST_P(UnitSubstituteTests, SubstitutesUnderNestedTerms)
{
  Sort arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  Term arr = s->make_symbol("arr", arrsort);
  Term arr0 = s->make_symbol("arr0", arrsort);
  Term idx = s->make_symbol("idx", bvsort);
  Term idx0 = s->make_symbol("idx0", bvsort);
  Term w = s->make_symbol("w", bvsort);
  auto constraint = [&](Term array, Term index, Term u, Term v) {
    return s->make_term(Equal,
                        s->make_term(Select, array, index),
                        s->make_term(BVAdd, u, s->make_term(BVMul, v, w)));
  };
  // w is not in the map, so it stays
  Term result =
      s->substitute(constraint(arr, idx, x, y),
                    { { arr, arr0 }, { idx, idx0 }, { x, a }, { y, b } });
  EXPECT_EQ(result, constraint(arr0, idx0, a, b));
}

TEST_P(UnitSubstituteTests, SubstitutesUnderApplication)
{
  Term g = s->make_symbol(
      "g", s->make_sort(FUNCTION, SortVec{ bvsort, bvsort, bvsort }));
  Term result = s->substitute(s->make_term(Apply, g, x, y), { { x, a } });
  EXPECT_EQ(result, s->make_term(Apply, g, a, y));
  EXPECT_EQ(result->get_op(), Apply);
}

TEST_P(UnitSubstituteIterTests, SimpleSubstitution)
{
  UnorderedTermMap subs_map({ { x, a }, { y, b } });
  Term apb = s->substitute(xpy, subs_map);

  UnorderedTermSet free_syms;
  get_free_symbolic_consts(apb, free_syms);
  EXPECT_EQ(free_syms.size(), 2);

  for (auto v : { a, b })
  {
    EXPECT_TRUE(free_syms.find(v) != free_syms.end());
  }
}

TEST_P(UnitSubstituteTests, SubstituteTerms)
{
  UnorderedTermMap subs_map({ { x, a }, { y, b } });
  Term apb = s->substitute(xpy, subs_map);
  TermVec subs = s->substitute_terms({ x, y, xpy }, subs_map);

  ASSERT_EQ(subs.size(), 3);
  EXPECT_EQ(subs[0], a);
  EXPECT_EQ(subs[1], b);
  EXPECT_EQ(subs[2], apb);
}

TEST_P(UnitSubstituteTests, SimpleSubstitutionWalker)
{
  // substitution walker can substitute arbitrary terms
  // not just symbol keys
  Term apb_spec = s->make_term(BVAdd, a, b);
  UnorderedTermMap subs_map({ { xpy, apb_spec } });
  SubstitutionWalker sw(s, subs_map);

  Term apb = sw.visit(xpy);
  EXPECT_EQ(apb, apb_spec);

  // test it again to make sure not corrupted
  apb = sw.visit(xpy);
  EXPECT_EQ(apb, apb_spec);
}

TEST_P(UnitSubstituteTests, BadSubstitution)
{
  Sort diff_bvsort = s->make_sort(BV, bvsort->get_width() + 1);
  Term newvar = s->make_symbol("newvar", diff_bvsort);

  EXPECT_THROW(SubstitutionWalker(s, { { x, newvar } }),
               IncorrectUsageException);
}

INSTANTIATE_TEST_SUITE_P(ParametrizedUnitSubstitute,
                         UnitSubstituteTests,
                         testing::ValuesIn(available_solver_configurations()));

INSTANTIATE_TEST_SUITE_P(
    ParametrizedUnitSubstitute,
    UnitSubstituteIterTests,
    testing::ValuesIn(filter_solver_configurations({ TERMITER })));

}  // namespace
