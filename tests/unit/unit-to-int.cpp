/*********************                                                        */
/*! \file unit-to-int.cpp
** \verbatim
** Top contributors (to current version):
**   Áron Ricardo Perez-Lopez
** This file is part of the smt-switch project.
** Copyright (c) 2026 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for Term::to_int and Term::to_signed_int, on constants and
**        on model values, which some solvers print differently.
**/
#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <limits>
#include <string>
#include <utility>

#include "available_solvers.h"
#include "exceptions.h"
#include "generic_sort.h"
#include "generic_term.h"
#include "smt.h"
#include "utils.h"

using namespace smt;
using namespace std;

namespace smt_tests {

namespace {

const uint64_t uint64_max = numeric_limits<uint64_t>::max();
const int64_t int64_max = numeric_limits<int64_t>::max();
const int64_t int64_min = numeric_limits<int64_t>::min();

}  // namespace

class ToIntTests : public ::testing::Test,
                   public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    s->set_opt("incremental", "true");
  }

  /** Returns the value a model gives a fresh symbol constrained to equal t */
  Term model_value(const Term & t)
  {
    Term x = s->make_symbol("x" + std::to_string(num_symbols++), t->get_sort());
    s->push();
    s->assert_formula(s->make_term(Equal, x, t));
    Result r = s->check_sat();
    EXPECT_TRUE(r.is_sat());
    Term v = s->get_value(x);
    s->pop();
    return v;
  }

  /** Returns the value t, followed by the same value from a model */
  TermVec with_model_value(const Term & t) { return { t, model_value(t) }; }

  /** Like with_model_value, for a negative t. The generic solver drops the
   *  sign when it reads back a negative value such as (- 5) from a model,
   *  so it only gets the constant.
   */
  TermVec with_negative_model_value(const Term & t)
  {
    if (GetParam().solver_enum == GENERIC_SOLVER)
    {
      return { t };
    }
    return with_model_value(t);
  }

  SmtSolver s;
  size_t num_symbols = 0;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ToIntBVTests);
class ToIntBVTests : public ToIntTests
{
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ToIntIntTests);
class ToIntIntTests : public ToIntTests
{
 protected:
  /** Makes the integer i. MathSAT's make_term from an int64_t truncates it
   *  to an int, and Yices2's make_term from a string parses it with stoi,
   *  so each solver gets the one that works for it.
   */
  Term make_int64(int64_t i)
  {
    Sort intsort = s->make_sort(INT);
    if (GetParam().solver_enum == YICES2)
    {
      return s->make_term(i, intsort);
    }
    return s->make_term(std::to_string(i), intsort);
  }

  /** Returns the integer n, outside the int64_t range, and equal to the
   *  sum of the addends: as a constant made from the string n, then as a
   *  model value of the sum. Yices2 gets no constant, having no way to make
   *  one outside the int64_t range (see make_int64), and the generic solver
   *  no model value for a negative n (see with_negative_model_value).
   */
  TermVec big_int_values(const std::string & n,
                         std::initializer_list<int64_t> addends)
  {
    TermVec res;
    if (GetParam().solver_enum != YICES2)
    {
      res.push_back(s->make_term(n, s->make_sort(INT)));
    }
    if (n[0] != '-' || GetParam().solver_enum != GENERIC_SOLVER)
    {
      Term sum;
      for (int64_t a : addends)
      {
        sum = sum ? s->make_term(Plus, sum, make_int64(a)) : make_int64(a);
      }
      res.push_back(model_value(sum));
    }
    return res;
  }
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ToIntRealTests);
class ToIntRealTests : public ToIntTests
{
};

TEST_P(ToIntBVTests, Unsigned)
{
  Sort bv32 = s->make_sort(BV, 32);
  Sort bv64 = s->make_sort(BV, 64);
  const std::pair<Term, uint64_t> cases[] = {
    { s->make_term(0, bv64), 0 },
    { s->make_term("2147483648", bv32, 10), uint64_t(1) << 31 },
    { s->make_term("2147483648", bv64, 10), uint64_t(1) << 31 },
    { s->make_term("9223372036854775808", bv64, 10), uint64_t(1) << 63 },
    { s->make_term("18446744073709551615", bv64, 10), uint64_max },
  };
  for (const auto & c : cases)
  {
    for (const Term & v : with_model_value(c.first))
    {
      SCOPED_TRACE(v->to_string());
      EXPECT_EQ(v->to_int(), c.second);
    }
  }
}

TEST_P(ToIntBVTests, Signed)
{
  Sort bv4 = s->make_sort(BV, 4);
  Sort bv64 = s->make_sort(BV, 64);
  const std::pair<Term, int64_t> cases[] = {
    { s->make_term("0000", bv4, 2), 0 },
    { s->make_term("1111", bv4, 2), -1 },
    { s->make_term("0111", bv4, 2), 7 },
    { s->make_term("1000", bv4, 2), -8 },
    { s->make_term("0", bv64, 10), 0 },
    { s->make_term("18446744073709551615", bv64, 10), -1 },
    { s->make_term("9223372036854775807", bv64, 10), int64_max },
    { s->make_term("9223372036854775808", bv64, 10), int64_min },
  };
  for (const auto & c : cases)
  {
    for (const Term & v : with_model_value(c.first))
    {
      SCOPED_TRACE(v->to_string());
      EXPECT_EQ(v->to_signed_int(), c.second);
    }
  }

  // the same bits, read as unsigned
  EXPECT_EQ(s->make_term("1111", bv4, 2)->to_int(), uint64_t(15));
  EXPECT_EQ(s->make_term("1000", bv4, 2)->to_int(), uint64_t(8));
}

TEST_P(ToIntBVTests, WiderThan64Bits)
{
  // no bit-vector wider than 64 bits converts, whatever its value
  for (uint64_t width : { 65, 128 })
  {
    Sort sort = s->make_sort(BV, width);
    for (const Term & v : with_model_value(s->make_term(1, sort)))
    {
      SCOPED_TRACE(v->to_string());
      EXPECT_THROW(v->to_int(), IncorrectUsageException);
      EXPECT_THROW(v->to_signed_int(), IncorrectUsageException);
    }
  }
}

TEST_P(ToIntBVTests, NotAValue)
{
  Term x = s->make_symbol("y", s->make_sort(BV, 8));
  EXPECT_THROW(x->to_int(), IncorrectUsageException);
  EXPECT_THROW(x->to_signed_int(), IncorrectUsageException);
}

TEST_P(ToIntIntTests, InRange)
{
  for (int64_t i : { int64_t(0), int64_t(5), int64_t(1) << 40, int64_max })
  {
    for (const Term & v : with_model_value(make_int64(i)))
    {
      SCOPED_TRACE(v->to_string());
      EXPECT_EQ(v->to_int(), static_cast<uint64_t>(i));
      EXPECT_EQ(v->to_signed_int(), i);
    }
  }
}

TEST_P(ToIntIntTests, Negative)
{
  for (int64_t i : { int64_t(-5), int64_min })
  {
    for (const Term & v : with_negative_model_value(make_int64(i)))
    {
      SCOPED_TRACE(v->to_string());
      EXPECT_THROW(v->to_int(), IncorrectUsageException);
      EXPECT_EQ(v->to_signed_int(), i);
    }
  }
}

TEST_P(ToIntIntTests, AboveInt64Max)
{
  for (const Term & v : big_int_values("9223372036854775808", { int64_max, 1 }))
  {
    SCOPED_TRACE(v->to_string());
    EXPECT_EQ(v->to_int(), uint64_t(1) << 63);
    EXPECT_THROW(v->to_signed_int(), IncorrectUsageException);
  }
  for (const Term & v :
       big_int_values("18446744073709551615", { int64_max, int64_max, 1 }))
  {
    SCOPED_TRACE(v->to_string());
    EXPECT_EQ(v->to_int(), uint64_max);
    EXPECT_THROW(v->to_signed_int(), IncorrectUsageException);
  }
}

TEST_P(ToIntIntTests, OutOfRange)
{
  TermVec values =
      big_int_values("18446744073709551616", { int64_max, int64_max, 2 });
  for (const Term & v :
       big_int_values("-9223372036854775809", { int64_min, -1 }))
  {
    values.push_back(v);
  }
  for (const Term & v : values)
  {
    SCOPED_TRACE(v->to_string());
    EXPECT_THROW(v->to_int(), IncorrectUsageException);
    EXPECT_THROW(v->to_signed_int(), IncorrectUsageException);
  }
}

TEST_P(ToIntIntTests, NotAValue)
{
  Term x = s->make_symbol("y", s->make_sort(INT));
  EXPECT_THROW(x->to_int(), IncorrectUsageException);
  EXPECT_THROW(x->to_signed_int(), IncorrectUsageException);
}

TEST_P(ToIntRealTests, IntegralValue)
{
  Sort realsort = s->make_sort(REAL);
  for (const Term & v : with_model_value(s->make_term(2, realsort)))
  {
    SCOPED_TRACE(v->to_string());
    EXPECT_EQ(v->to_int(), uint64_t(2));
    EXPECT_EQ(v->to_signed_int(), 2);
  }
  // not -2: Z3 terms compare by hash, and the hashes of 2.0 and -2.0 collide,
  // so the logging solver would hand back the 2.0 it already has
  for (const Term & v : with_model_value(s->make_term(-3, realsort)))
  {
    SCOPED_TRACE(v->to_string());
    EXPECT_THROW(v->to_int(), IncorrectUsageException);
    EXPECT_EQ(v->to_signed_int(), -3);
  }
}

TEST_P(ToIntRealTests, NonIntegralValue)
{
  Sort realsort = s->make_sort(REAL);
  Term half =
      s->make_term(Div, s->make_term(1, realsort), s->make_term(2, realsort));
  Term v = model_value(half);
  SCOPED_TRACE(v->to_string());
  EXPECT_THROW(v->to_int(), IncorrectUsageException);
  EXPECT_THROW(v->to_signed_int(), IncorrectUsageException);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverToIntBVTests,
    ToIntBVTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_BV })));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverToIntIntTests,
    ToIntIntTests,
    testing::ValuesIn(filter_solver_configurations({ THEORY_INT })));

// not the generic solver, which declares a real value made from an integer,
// such as 2, with an integer literal that cvc5 rejects as a Real
INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverToIntRealTests,
    ToIntRealTests,
    testing::ValuesIn(
        filter_non_generic_solver_configurations({ THEORY_REAL })));

// SMT-LIB numerals are never negative: a negative integer value is (- n)
TEST(ToIntParsing, SmtlibNegativeInt)
{
  EXPECT_EQ(smtlib_int_to_int64("(- 5)"), -5);
  EXPECT_EQ(smtlib_int_to_int64("(- 9223372036854775808)"), int64_min);
  EXPECT_EQ(smtlib_int_to_int64("(- 5.0)"), -5);
  EXPECT_THROW(smtlib_int_to_uint64("(- 5)"), IncorrectUsageException);
  EXPECT_THROW(smtlib_int_to_int64("(- 9223372036854775809)"),
               IncorrectUsageException);
  EXPECT_THROW(smtlib_int_to_int64("(- (- 5))"), IncorrectUsageException);
  EXPECT_THROW(smtlib_int_to_int64("(/ (- 1) 2)"), IncorrectUsageException);
}

// -5 is an SMT-LIB symbol, but Yices2 and MathSAT print values this way
TEST(ToIntParsing, SignedLiteral)
{
  EXPECT_EQ(smtlib_int_to_int64("-5"), -5);
  EXPECT_THROW(smtlib_int_to_uint64("-5"), IncorrectUsageException);
  EXPECT_EQ(smtlib_int_to_uint64("-0"), 0u);
}

TEST(ToIntParsing, IndexedBVOutOfRange)
{
  EXPECT_EQ(smtlib_bv_to_int64("(_ bv15 4)"), -1);
  EXPECT_THROW(smtlib_bv_to_uint64("(_ bv16 4)"), IncorrectUsageException);
  EXPECT_THROW(smtlib_bv_to_int64("(_ bv16 4)"), IncorrectUsageException);
}

// AbsTerm::to_signed_int is the default for Term implementations outside
// smt-switch; call it on a GenericTerm, whose repr is exactly what it reads
TEST(ToIntParsing, DefaultToSignedInt)
{
  GenericTerm neg(make_generic_sort(INT), Op(), {}, "(- 5)");
  EXPECT_EQ(neg.AbsTerm::to_signed_int(), -5);
  EXPECT_EQ(neg.to_signed_int(), -5);
  EXPECT_THROW(neg.to_int(), IncorrectUsageException);

  GenericTerm bv(make_generic_sort(BV, 4), Op(), {}, "#b1111");
  EXPECT_EQ(bv.AbsTerm::to_signed_int(), -1);

  GenericTerm x(make_generic_sort(INT), Op(), {}, "x", true);
  EXPECT_THROW(x.AbsTerm::to_signed_int(), IncorrectUsageException);

  GenericTerm b(make_generic_sort(BOOL), Op(), {}, "true");
  EXPECT_THROW(b.AbsTerm::to_signed_int(), IncorrectUsageException);
}

}  // namespace smt_tests
