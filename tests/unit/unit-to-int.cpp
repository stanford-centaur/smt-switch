/*!
 * \file unit-to-int.cpp
 * \brief Tests for Term::to_int, Term::to_signed_int and Term::to_bits, on
 *        constants and on model values, which some solvers print differently
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <limits>
#include <memory>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/generic_sort.h"
#include "smt-switch/generic_term.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/utils.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

const uint64_t uint64_max = numeric_limits<uint64_t>::max();
const int64_t int64_max = numeric_limits<int64_t>::max();
const int64_t int64_min = numeric_limits<int64_t>::min();

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
  /** Returns the integer n, outside the int64_t range, and equal to the
   *  sum of the addends: as a constant made from the string n, then as a
   *  model value of the sum
   */
  TermVec big_int_values(const std::string & n,
                         std::initializer_list<int64_t> addends)
  {
    Sort intsort = s->make_sort(INT);
    TermVec res = { s->make_term(n, intsort) };
    Term sum;
    for (int64_t a : addends)
    {
      Term addend = s->make_term(a, intsort);
      sum = sum ? s->make_term(Plus, sum, addend) : addend;
    }
    res.push_back(model_value(sum));
    return res;
  }
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ToIntRealTests);
class ToIntRealTests : public ToIntTests
{
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ToBits);
class ToBits : public ToIntTests
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
    { s->make_term("0F", bv32, 16), 15 },
    { s->make_term("80000000", bv32, 16), uint64_t(1) << 31 },
    { s->make_term("ffffffffffffffff", bv64, 16), uint64_max },
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
    { s->make_term(-8, bv4), -8 },
    { s->make_term("-1", bv4, 10), -1 },
    { s->make_term("-1099511627776", bv64, 10), -1099511627776 },
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

TEST_P(ToIntBVTests, MadeFromInt64)
{
  // values that need more than 32 bits
  Sort bv64 = s->make_sort(BV, 64);
  for (int64_t i : { int64_min, int64_t(1) << 40, -(int64_t(1) << 40) })
  {
    Term v = model_value(s->make_term(i, bv64));
    SCOPED_TRACE(v->to_string());
    EXPECT_EQ(v->to_signed_int(), i);
  }
}

TEST_P(ToIntBVTests, WideValueThatFits)
{
  for (uint64_t width : { 65, 128, 1024 })
  {
    Sort sort = s->make_sort(BV, width);
    for (const Term & v : with_model_value(s->make_term("2", sort, 10)))
    {
      SCOPED_TRACE(v->to_string());
      EXPECT_EQ(v->to_int(), 2u);
      EXPECT_EQ(v->to_signed_int(), 2);
    }
    for (const Term & v :
         with_model_value(s->make_term("18446744073709551615", sort, 10)))
    {
      SCOPED_TRACE(v->to_string());
      EXPECT_EQ(v->to_int(), uint64_max);
      EXPECT_THROW(v->to_signed_int(), IncorrectUsageException);
    }
    for (const Term & v : with_model_value(s->make_term("-1", sort, 10)))
    {
      SCOPED_TRACE(v->to_string());
      EXPECT_THROW(v->to_int(), IncorrectUsageException);
      EXPECT_EQ(v->to_signed_int(), -1);
    }
    for (const Term & v :
         with_model_value(s->make_term("-9223372036854775808", sort, 10)))
    {
      SCOPED_TRACE(v->to_string());
      EXPECT_THROW(v->to_int(), IncorrectUsageException);
      EXPECT_EQ(v->to_signed_int(), int64_min);
    }
  }
}

TEST_P(ToIntBVTests, WideValueThatDoesNotFit)
{
  for (uint64_t width : { 65, 128, 1024 })
  {
    Sort sort = s->make_sort(BV, width);
    const char * const values[] = { "18446744073709551616",
                                    "-9223372036854775809" };
    for (const char * value : values)
    {
      for (const Term & v : with_model_value(s->make_term(value, sort, 10)))
      {
        SCOPED_TRACE(v->to_string());
        EXPECT_THROW(v->to_int(), IncorrectUsageException);
        EXPECT_THROW(v->to_signed_int(), IncorrectUsageException);
      }
    }
  }
  // 2^63 is unsigned, but its top bit is not the sign bit of 65 bits
  Sort bv65 = s->make_sort(BV, 65);
  for (const Term & v :
       with_model_value(s->make_term("9223372036854775808", bv65, 10)))
  {
    SCOPED_TRACE(v->to_string());
    EXPECT_EQ(v->to_int(), uint64_t(1) << 63);
    EXPECT_THROW(v->to_signed_int(), IncorrectUsageException);
  }
}

TEST_P(ToIntBVTests, ConstantNeedsNoModel)
{
  Sort bv4 = s->make_sort(BV, 4);
  Term five = s->make_term(5, bv4);
  Term minus_three = s->make_term(-3, bv4);
  EXPECT_EQ(five->to_int(), 5u);
  EXPECT_EQ(minus_three->to_signed_int(), -3);

  s->assert_formula(s->make_term(false));
  ASSERT_TRUE(s->check_sat().is_unsat());
  EXPECT_EQ(five->to_int(), 5u);
  EXPECT_EQ(minus_three->to_signed_int(), -3);
}

TEST_P(ToIntBVTests, NotAValue)
{
  Term x = s->make_symbol("y", s->make_sort(BV, 8));
  EXPECT_THROW(x->to_int(), IncorrectUsageException);
  EXPECT_THROW(x->to_signed_int(), IncorrectUsageException);
}

TEST_P(ToIntIntTests, InRange)
{
  Sort intsort = s->make_sort(INT);
  for (int64_t i : { int64_t(0), int64_t(5), int64_t(1) << 40, int64_max })
  {
    for (const Term & v : with_model_value(s->make_term(i, intsort)))
    {
      SCOPED_TRACE(v->to_string());
      EXPECT_EQ(v->to_int(), static_cast<uint64_t>(i));
      EXPECT_EQ(v->to_signed_int(), i);
    }
  }
}

TEST_P(ToIntIntTests, Negative)
{
  Sort intsort = s->make_sort(INT);
  for (int64_t i : { int64_t(-5), int64_min })
  {
    for (const Term & v : with_model_value(s->make_term(i, intsort)))
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
  for (const Term & v : with_model_value(s->make_term(-2, realsort)))
  {
    SCOPED_TRACE(v->to_string());
    EXPECT_THROW(v->to_int(), IncorrectUsageException);
    EXPECT_EQ(v->to_signed_int(), -2);
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

TEST_P(ToBits, Values)
{
  const std::pair<Term, std::string> cases[] = {
    { s->make_term(1, s->make_sort(BV, 1)), "1" },
    { s->make_term(5, s->make_sort(BV, 4)), "0101" },
    { s->make_term(-2, s->make_sort(BV, 8)), "11111110" },
    { s->make_term(0, s->make_sort(BV, 64)), std::string(64, '0') },
    { s->make_term("-1", s->make_sort(BV, 65), 10), std::string(65, '1') },
    { s->make_term("2", s->make_sort(BV, 1024), 10),
      std::string(1022, '0') + "10" },
  };
  for (const auto & c : cases)
  {
    for (const Term & v : with_model_value(c.first))
    {
      SCOPED_TRACE(v->to_string());
      EXPECT_EQ(v->to_bits(), c.second);
    }
  }
}

TEST_P(ToBits, NotAValue)
{
  Term x = s->make_symbol("y", s->make_sort(BV, 8));
  EXPECT_THROW(x->to_bits(), IncorrectUsageException);
}

INSTANTIATE_TEST_SUITE_P(
    UnitToInt,
    ToBits,
    testing::ValuesIn(filter_solver_configurations_with_generic({ THEORY_BV })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverToIntBVTests,
    ToIntBVTests,
    testing::ValuesIn(
        filter_solver_configurations_with_generic({ THEORY_BV })));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverToIntIntTests,
    ToIntIntTests,
    testing::ValuesIn(
        filter_solver_configurations_with_generic({ THEORY_INT })));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverToIntRealTests,
    ToIntRealTests,
    testing::ValuesIn(
        filter_solver_configurations_with_generic({ THEORY_REAL })));

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

TEST(ToIntParsing, HexBV)
{
  EXPECT_EQ(smtlib_bv_to_uint64("#xfF"), 255u);
  EXPECT_EQ(smtlib_bv_to_int64("#xff"), -1);
  EXPECT_THROW(smtlib_bv_to_uint64("#xg0"), IncorrectUsageException);
}

TEST(ToIntParsing, IndexedBVOutOfRange)
{
  EXPECT_EQ(smtlib_bv_to_int64("(_ bv15 4)"), -1);
  EXPECT_THROW(smtlib_bv_to_uint64("(_ bv16 4)"), IncorrectUsageException);
  EXPECT_THROW(smtlib_bv_to_int64("(_ bv16 4)"), IncorrectUsageException);
}

TEST(ToIntParsing, BVToBits)
{
  EXPECT_EQ(smtlib_bv_to_bits("#b0101"), "0101");
  EXPECT_EQ(smtlib_bv_to_bits("#x0a"), "00001010");
  EXPECT_EQ(smtlib_bv_to_bits("(_ bv5 8)"), "00000101");
  EXPECT_EQ(smtlib_bv_to_bits("(_ bv2 1024)"), std::string(1022, '0') + "10");
  for (const char * s : { "#b",
                          "#x",
                          "#b012",
                          "#xg",
                          "(_ bv16 4)",
                          "(_ bv1 0)",
                          "(_ bv 4)",
                          "5" })
  {
    SCOPED_TRACE(s);
    EXPECT_THROW(smtlib_bv_to_bits(s), IncorrectUsageException);
  }
}

TEST(ToIntParsing, WideBV)
{
  EXPECT_EQ(smtlib_bv_to_uint64("(_ bv2 1024)"), 2u);
  EXPECT_EQ(smtlib_bv_to_int64("(_ bv2 1024)"), 2);
  EXPECT_EQ(smtlib_bv_to_uint64("#x0ffffffffffffffff"), uint64_max);
  EXPECT_THROW(smtlib_bv_to_int64("#x0ffffffffffffffff"),
               IncorrectUsageException);
  EXPECT_EQ(smtlib_bv_to_int64("#xfffffffffffffffff"), -1);
  EXPECT_EQ(bits_to_int64(std::string(65, '1')), -1);
  EXPECT_THROW(bits_to_uint64(std::string(65, '1')), IncorrectUsageException);
  EXPECT_THROW(smtlib_bv_to_uint64("(_ bv18446744073709551616 65)"),
               IncorrectUsageException);
  // 2^65 - 1 is all ones in 65 bits
  EXPECT_EQ(smtlib_bv_to_int64("(_ bv36893488147419103231 65)"), -1);
}

// AbsTerm::to_signed_int is the default for Term implementations outside
// smt-switch; call it on a GenericTerm, whose repr is exactly what it reads
TEST(ToIntParsing, DefaultToSignedInt)
{
  GenericTerm neg(std::make_shared<GenericSort>(INT), Op(), {}, "(- 5)");
  EXPECT_EQ(neg.AbsTerm::to_signed_int(), -5);
  EXPECT_EQ(neg.to_signed_int(), -5);
  EXPECT_THROW(neg.to_int(), IncorrectUsageException);

  GenericTerm bv(std::make_shared<BVGenericSort>(4), Op(), {}, "#b1111");
  EXPECT_EQ(bv.AbsTerm::to_signed_int(), -1);

  GenericTerm x(std::make_shared<GenericSort>(INT), Op(), {}, "x", true);
  EXPECT_THROW(x.AbsTerm::to_signed_int(), IncorrectUsageException);

  GenericTerm b(std::make_shared<GenericSort>(BOOL), Op(), {}, "true");
  EXPECT_THROW(b.AbsTerm::to_signed_int(), IncorrectUsageException);
}

}  // namespace
