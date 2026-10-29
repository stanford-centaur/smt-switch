/*********************                                                        */
/*! \file unit-termiter.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for term iteration.
**
**
**/

#include <gtest/gtest.h>

#include <algorithm>
#include <memory>
#include <string>
#include <type_traits>
#include <unordered_set>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "exceptions.h"
#include "identity_walker.h"
#include "ops.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"
#include "term_utils.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTests);
class UnitTests : public ::testing::Test,
                  public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  }
  SmtSolver s;
  Sort bvsort, funsort, arrsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ConstArrUnitTests);
class ConstArrUnitTests : public UnitTests
{
};

TEST_P(UnitTests, TermIter)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  TermIter it = fx->begin();
  TermIter it2;
  it2 = it;

  EXPECT_EQ(it, it);
  EXPECT_EQ(it, it2);
}

TEST_P(UnitTests, NestedApplication)
{
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term g = s->make_symbol(
      "g", s->make_sort(FUNCTION, SortVec{ bvsort, bvsort, bvsort }));
  Term gxy = s->make_term(Apply, g, x, y);
  Term eq = s->make_term(Equal, gxy, x);
  // the solver may order the children either way
  TermVec children(eq->begin(), eq->end());
  auto it = std::find(children.begin(), children.end(), gxy);
  ASSERT_NE(it, children.end());
  EXPECT_EQ((*it)->get_op(), Apply);
  ASSERT_NE((*it)->begin(), (*it)->end());
  EXPECT_EQ((*(*it)->begin())->get_sort()->get_sort_kind(), FUNCTION);
}

TEST_P(ConstArrUnitTests, ConstArr)
{
  Term zero = s->make_term(0, bvsort);
  Term constarr = s->make_term(zero, arrsort);
  ASSERT_TRUE(constarr->get_op().is_null());
  ASSERT_TRUE(constarr->get_sort() == arrsort);
  ASSERT_TRUE(constarr->get_sort()->get_indexsort() == bvsort);
  ASSERT_TRUE(constarr->get_sort()->get_elemsort() == bvsort);
}

TEST_P(ConstArrUnitTests, IdentityWalker)
{
  if (GetParam().solver_enum == YICES2)
  {
    GTEST_SKIP() << "Yices2 cannot read a constant array through a store at "
                    "a symbolic index";
  }

  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term arr = s->make_symbol("arr", arrsort);
  Term f = s->make_symbol("f", funsort);

  Term fx = s->make_term(Apply, f, x);
  Term ypfx = s->make_term(BVAdd, y, fx);
  Term xmy = s->make_term(BVMul, y, x);
  Term shift = s->make_term(BVShl, xmy, ypfx);
  Term constarr = s->make_term(s->make_term(0, bvsort), arrsort);

  Term store_0 = s->make_term(Store, constarr, x, xmy);
  Term store_1 = s->make_term(Store, store_0, y, shift);
  Term final_term = s->make_term(Select, store_1, ypfx);

  IdentityWalker iw(s, false);  // don't clear the cache between calls
  Term id_final_term = iw.visit(final_term);
  ASSERT_TRUE(round_trip_matches(GetParam(), s, id_final_term, final_term));
}

TEST_P(UnitTests, InputIterator)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);
  TermVec children(fx->begin(), fx->end());
  ASSERT_EQ(children[0], f);
  ASSERT_EQ(children[1], x);
}

TEST_P(UnitTests, ConstTermRangeFor)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  const Term fx = s->make_term(Apply, f, x);

  TermVec children;
  for (const Term & c : fx)
  {
    children.push_back(c);
  }
  EXPECT_EQ(children, TermVec(fx->begin(), fx->end()));
}

TEST_P(UnitTests, CopyIter)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  Term v = s->make_symbol("v", bvsort);
  Term fv = s->make_term(Apply, f, v);

  ASSERT_NE(fx, fv);

  TermIter it1 = fx->begin();
  TermIter it2 = fx->begin();
  EXPECT_EQ(it1, it2);
  TermIter it3 = fv->begin();
  EXPECT_NE(it1, it3);
  it2 = it3;
  EXPECT_NE(it1, it2);
}

TEST_P(UnitTests, CopyDefaultConstructedIter)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  TermIter empty;
  TermIter copy(empty);
  EXPECT_EQ(copy, empty);

  TermIter it = fx->begin();
  EXPECT_NE(it, empty);
  EXPECT_NE(empty, it);
  it = empty;
  EXPECT_EQ(it, empty);
}

TEST(NullTermIter, CannotBeDereferencedOrIncremented)
{
  TermIter it;
  EXPECT_THROW(*it, IncorrectUsageException);
  EXPECT_THROW(++it, IncorrectUsageException);
  EXPECT_THROW(it++, IncorrectUsageException);
}

// an iterator over nothing that only knows its position
class PositionIter : public TermIterBase
{
 public:
  explicit PositionIter(int p) : pos(p) {}
  void operator++() override { ++pos; }
  Term operator*() const override { return Term(); }
  TermIterBase * clone() const override { return new PositionIter(pos); }

 protected:
  bool equal(const TermIterBase & other) const override
  {
    return pos == static_cast<const PositionIter &>(other).pos;
  }

 private:
  int pos;
};

TEST(TermIterBase, InequalityNegatesEquality)
{
  PositionIter first(0), same(0), second(1);
  EXPECT_FALSE(first != same);
  EXPECT_TRUE(first != second);
}

TEST_P(UnitTests, SelfAssignIter)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  TermIter it = fx->begin();
  ++it;
  // through a reference, so the compiler does not warn about self-assignment
  TermIter & same = it;
  it = same;
  EXPECT_EQ(*it, x);
}

TEST_P(UnitTests, MoveIter)
{
  static_assert(std::is_nothrow_move_constructible<TermIter>::value,
                "TermIter moves without cloning");
  static_assert(std::is_nothrow_move_assignable<TermIter>::value,
                "TermIter moves without cloning");

  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  TermIter it = fx->begin();
  TermIter moved(std::move(it));
  EXPECT_EQ(*moved, f);

  TermIter assigned;
  assigned = std::move(moved);
  EXPECT_EQ(*assigned, f);
  ++assigned;
  EXPECT_EQ(*assigned, x);
}

INSTANTIATE_TEST_SUITE_P(
    ParametrizedUnit,
    UnitTests,
    testing::ValuesIn(filter_solver_configurations({ TERMITER })));

INSTANTIATE_TEST_SUITE_P(
    ParametrizedConstArrUnit,
    ConstArrUnitTests,
    testing::ValuesIn(filter_solver_configurations({ CONSTARR, TERMITER })));

}  // namespace
