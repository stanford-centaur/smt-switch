/*!
 * \file test-op-definitions.cpp
 * \brief Checks that operators mean what their definitions say.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Each check asserts that an operator and its definition in terms of other
 * operators can differ, and expects that to be unsatisfiable.
 */

#include <gtest/gtest.h>

#include <cstdint>

#include "available_solvers.h"
#include "smt.h"

using namespace smt;

namespace smt_tests {

class OpDefinitionTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("incremental", "true");
  }

  /** Expects term and definition to be equal in every model */
  void expect_equivalent(const Term & term, const Term & definition)
  {
    // Not and Equal rather than Distinct, which is under test itself
    expect_valid(s->make_term(Equal, term, definition));
  }

  /** Expects formula to hold in every model */
  void expect_valid(const Term & formula)
  {
    s->push();
    s->assert_formula(s->make_term(Not, formula));
    EXPECT_TRUE(s->check_sat().is_unsat()) << formula << " can be false";
    s->pop();
  }

  SmtSolver s;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(BoolOpDefinitionTests);
class BoolOpDefinitionTests : public OpDefinitionTests
{
 protected:
  void SetUp() override
  {
    OpDefinitionTests::SetUp();
    Sort boolsort = s->make_sort(BOOL);
    a = s->make_symbol("a", boolsort);
    b = s->make_symbol("b", boolsort);
    c = s->make_symbol("c", boolsort);
  }
  Term a, b, c;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(BVOpDefinitionTests);
class BVOpDefinitionTests : public OpDefinitionTests
{
 protected:
  void SetUp() override
  {
    OpDefinitionTests::SetUp();
    Sort bvsort = s->make_sort(BV, 8);
    x = s->make_symbol("x", bvsort);
    y = s->make_symbol("y", bvsort);
  }
  Term x, y;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IntOpDefinitionTests);
class IntOpDefinitionTests : public OpDefinitionTests
{
 protected:
  void SetUp() override
  {
    OpDefinitionTests::SetUp();
    Sort intsort = s->make_sort(INT);
    v = s->make_symbol("v", intsort);
    w = s->make_symbol("w", intsort);
    zero = s->make_term(0, intsort);
  }
  Term v, w, zero;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(RealOpDefinitionTests);
class RealOpDefinitionTests : public OpDefinitionTests
{
};

TEST_P(BoolOpDefinitionTests, Xor)
{
  expect_equivalent(s->make_term(Xor, a, b),
                    s->make_term(Or,
                                 s->make_term(And, a, s->make_term(Not, b)),
                                 s->make_term(And, s->make_term(Not, a), b)));
}

TEST_P(BoolOpDefinitionTests, Implies)
{
  expect_equivalent(
      s->make_term(Implies, a, b),
      s->make_term(Not, s->make_term(And, a, s->make_term(Not, b))));
}

TEST_P(BoolOpDefinitionTests, Distinct)
{
  expect_equivalent(s->make_term(Distinct, a, b),
                    s->make_term(Not, s->make_term(Equal, a, b)));
}

TEST_P(BoolOpDefinitionTests, Ite)
{
  Term ite = s->make_term(Ite, a, b, c);
  expect_valid(s->make_term(
      And,
      s->make_term(Implies, a, s->make_term(Equal, ite, b)),
      s->make_term(
          Implies, s->make_term(Not, a), s->make_term(Equal, ite, c))));
}

TEST_P(BVOpDefinitionTests, BVNand)
{
  expect_equivalent(s->make_term(BVNand, x, y),
                    s->make_term(BVNot, s->make_term(BVAnd, x, y)));
}

TEST_P(BVOpDefinitionTests, BVNor)
{
  expect_equivalent(s->make_term(BVNor, x, y),
                    s->make_term(BVNot, s->make_term(BVOr, x, y)));
}

TEST_P(BVOpDefinitionTests, BVXnor)
{
  expect_equivalent(s->make_term(BVXnor, x, y),
                    s->make_term(BVNot, s->make_term(BVXor, x, y)));
}

TEST_P(BVOpDefinitionTests, BVSmod)
{
  // the definition of bvsmod in the SMT-LIB logic QF_BV
  uint64_t width = x->get_sort()->get_width();
  Term zero_1bit = s->make_term(0, s->make_sort(BV, 1));
  Term one_1bit = s->make_term(1, s->make_sort(BV, 1));
  Term zero_width = s->make_term(0, s->make_sort(BV, width));

  Term msb_x = s->make_term(Op(Extract, width - 1, width - 1), x);
  Term msb_y = s->make_term(Op(Extract, width - 1, width - 1), y);
  Term x_nonneg = s->make_term(Equal, msb_x, zero_1bit);
  Term y_nonneg = s->make_term(Equal, msb_y, zero_1bit);
  Term x_neg = s->make_term(Equal, msb_x, one_1bit);
  Term y_neg = s->make_term(Equal, msb_y, one_1bit);

  Term abs_x = s->make_term(Ite, x_nonneg, x, s->make_term(BVNeg, x));
  Term abs_y = s->make_term(Ite, y_nonneg, y, s->make_term(BVNeg, y));
  Term u = s->make_term(BVUrem, abs_x, abs_y);

  Term smod_def = s->make_term(
      Ite,
      s->make_term(Equal, u, zero_width),
      u,
      s->make_term(Ite,
                   s->make_term(And, x_nonneg, y_nonneg),
                   u,
                   s->make_term(Ite,
                                s->make_term(And, x_neg, y_nonneg),
                                s->make_term(BVAdd, s->make_term(BVNeg, u), y),
                                s->make_term(Ite,
                                             s->make_term(And, x_nonneg, y_neg),
                                             s->make_term(BVAdd, u, y),
                                             s->make_term(BVNeg, u)))));

  expect_equivalent(s->make_term(BVSmod, x, y), smod_def);
}

TEST_P(BVOpDefinitionTests, BVUgt)
{
  expect_equivalent(s->make_term(BVUgt, x, y),
                    s->make_term(Not, s->make_term(BVUle, x, y)));
}

TEST_P(BVOpDefinitionTests, BVUge)
{
  expect_equivalent(s->make_term(BVUge, x, y),
                    s->make_term(Not, s->make_term(BVUlt, x, y)));
}

TEST_P(BVOpDefinitionTests, BVSgt)
{
  expect_equivalent(s->make_term(BVSgt, x, y),
                    s->make_term(Not, s->make_term(BVSle, x, y)));
}

TEST_P(BVOpDefinitionTests, BVSge)
{
  expect_equivalent(s->make_term(BVSge, x, y),
                    s->make_term(Not, s->make_term(BVSlt, x, y)));
}

TEST_P(IntOpDefinitionTests, Negate)
{
  expect_equivalent(s->make_term(Plus, w, s->make_term(Negate, w)), zero);
}

TEST_P(IntOpDefinitionTests, Abs)
{
  expect_valid(s->make_term(Ge, s->make_term(Abs, v), zero));
}

TEST_P(IntOpDefinitionTests, Minus)
{
  expect_equivalent(s->make_term(Minus, v, v), zero);
}

TEST_P(IntOpDefinitionTests, Lt)
{
  expect_equivalent(s->make_term(Lt, w, v),
                    s->make_term(Not, s->make_term(Ge, w, v)));
}

TEST_P(IntOpDefinitionTests, Gt)
{
  expect_equivalent(s->make_term(Gt, w, v),
                    s->make_term(Not, s->make_term(Le, w, v)));
}

TEST_P(IntOpDefinitionTests, Ge)
{
  expect_equivalent(s->make_term(Ge, w, v),
                    s->make_term(Not, s->make_term(Lt, w, v)));
}

TEST_P(IntOpDefinitionTests, Ite)
{
  Term cond = s->make_symbol("cond", s->make_sort(BOOL));
  Term ite = s->make_term(Ite, cond, v, w);
  expect_valid(s->make_term(
      And,
      s->make_term(Implies, cond, s->make_term(Equal, ite, v)),
      s->make_term(
          Implies, s->make_term(Not, cond), s->make_term(Equal, ite, w))));
}

TEST_P(RealOpDefinitionTests, IsInt)
{
  Term one_point_three = s->make_term("1.3", s->make_sort(REAL));
  expect_valid(s->make_term(Not, s->make_term(Is_Int, one_point_three)));
}

INSTANTIATE_TEST_SUITE_P(,
                         BoolOpDefinitionTests,
                         testing::ValuesIn(available_solver_configurations()),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ,
    BVOpDefinitionTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_BV })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ,
    IntOpDefinitionTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_INT })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(,
                         RealOpDefinitionTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { THEORY_INT, THEORY_REAL })),
                         ConfigName());

}  // namespace smt_tests
