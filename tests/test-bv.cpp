/*********************                                                        */
/*! \file test-bv.cpp
** \verbatim
** Top contributors (to current version):
**  Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for theory of bit-vectors.
**
**
**/

#include <cstdint>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(BVTests);
class BVTests : public ::testing::Test,
                public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    s->set_opt("incremental", "true");
  }
  SmtSolver s;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IndexedOpTests);
class IndexedOpTests : public BVTests
{
};

// based on issue #308
TEST_P(BVTests, to_int)
{
  Sort sort1 = s->make_sort(BV, 1);
  Sort sort2 = s->make_sort(BV, 2);
  Term x1 = s->make_symbol("x1", sort1);
  Term x2 = s->make_symbol("x2", sort2);
  s->check_sat();
  uint64_t i1 = s->get_value(x1)->to_int();
  uint64_t i2 = s->get_value(x2)->to_int();
  ASSERT_LE(i1, 1);
  ASSERT_LE(i2, 3);

  Sort bv3 = s->make_sort(BV, 3);
  Term minus_one = s->make_term(-1, bv3);
  Term one = s->make_term(1, bv3);
  Term x = s->make_symbol("x", bv3);
  s->assert_formula(s->make_term(BVSlt, minus_one, x));
  s->assert_formula(s->make_term(BVSlt, x, one));
  s->check_sat();
  EXPECT_EQ(s->get_value(x)->to_int(), 0);
}

TEST_P(BVTests, SortsTermsAndModels)
{
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term y = s->make_symbol("y", bvsort8);
  Term z = s->make_symbol("z", bvsort8);
  EXPECT_NE(x, y);

  Sort xsort = x->get_sort();
  EXPECT_EQ(xsort, y->get_sort());

  Sort arr_sort = s->make_sort(ARRAY, s->make_sort(BV, 4), bvsort8);
  EXPECT_NE(xsort, arr_sort);
  EXPECT_NE(xsort, arr_sort->get_indexsort());
  EXPECT_EQ(xsort, arr_sort->get_elemsort());

  Term xpy = s->make_term(BVAdd, x, y);
  EXPECT_TRUE(x->is_symbolic_const());
  EXPECT_FALSE(xpy->is_symbolic_const());

  Term x_lower = s->make_term(Op(Extract, 3, 0), x);
  Term x_ext = s->make_term(Op(Zero_Extend, 4), x_lower);

  Sort funsort = s->make_sort(FUNCTION, SortVec{ x_lower->get_sort(), xsort });
  Term uf = s->make_symbol("f", funsort);
  Term uf_app = s->make_term(Apply, uf, x_lower);

  s->assert_formula(s->make_term(Equal, z, xpy));
  s->assert_formula(s->make_term(BVUlt, x, s->make_term(4, bvsort8)));
  s->assert_formula(s->make_term(BVUlt, y, s->make_term(4, bvsort8)));
  s->assert_formula(s->make_term(BVUgt, z, s->make_term("5", bvsort8)));
  // redundant, since x < 4 fits in its lower four bits
  s->assert_formula(s->make_term(Equal, x_ext, x));
  s->assert_formula(s->make_term(Distinct, x, z));
  s->assert_formula(s->make_term(BVUle, uf_app, s->make_term(3, bvsort8)));
  s->assert_formula(
      s->make_term(BVUge, uf_app, s->make_term("00000011", bvsort8, 2)));

  ASSERT_TRUE(s->check_sat().is_sat());

  // x, y < 4 and x + y > 5 leave only x = y = 3
  EXPECT_EQ(s->get_value(x)->to_int(), 3);
  EXPECT_EQ(s->get_value(y)->to_int(), 3);
  EXPECT_EQ(s->get_value(z)->to_int(), 6);
  EXPECT_EQ(s->get_value(x_ext)->to_int(), 3);
  EXPECT_EQ(s->get_value(x_lower)->to_int(), 3);
  EXPECT_EQ(s->get_value(uf_app)->to_int(), 3);
}

TEST_P(IndexedOpTests, RotateExtractRepeat)
{
  Sort bvsort9 = s->make_sort(BV, 9);
  Term x = s->make_symbol("x", bvsort9);
  Term y = s->make_symbol("y", bvsort9);
  Term onebit = s->make_symbol("onebit", s->make_sort(BV, 1));

  Term unnecessary_rotation = s->make_term(Op(Rotate_Right, 1), onebit);

  Op ext74 = Op(Extract, 7, 4);
  Term x_upper = s->make_term(ext74, x);

  Term y_ror = s->make_term(Op(Rotate_Right, 2), y);
  Term y_rol = s->make_term(Op(Rotate_Left, 2), y);

  s->assert_formula(s->make_term(Equal, y_ror, y_rol));
  s->assert_formula(s->make_term(Distinct, y, s->make_term(0, bvsort9)));
  s->assert_formula(s->make_term(
      Equal, x, s->make_term(Op(Repeat, 9), unnecessary_rotation)));

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  // ror 2 = rol 2 makes y invariant under rotation by 4, which on 9 bits
  // (gcd(4, 9) = 1) makes all its bits equal; y != 0, so y is all ones
  EXPECT_EQ(s->get_value(y)->to_int(), 0b1'1111'1111);
  // x repeats one bit nine times, so it and its slice x_upper are all zeros
  // or all ones
  auto x_val = s->get_value(x)->to_int();
  EXPECT_TRUE(x_val == 0 || x_val == 0b1'1111'1111);
  EXPECT_EQ(s->get_value(x_upper)->to_int(),
            x_val == 0b1'1111'1111 ? 0b1111 : 0);
}

TEST_P(IndexedOpTests, RepeatZeroTimes)
{
  Term x = s->make_symbol("x", s->make_sort(BV, 4));
  EXPECT_THROW(s->make_term(Op(Repeat, 0), x), IncorrectUsageException);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverBVTests,
    BVTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_BV })));

INSTANTIATE_TEST_SUITE_P(
    ,
    IndexedOpTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_BV })),
    ConfigName());

}  // namespace
