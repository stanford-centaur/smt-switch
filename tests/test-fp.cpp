/*********************                                                        */
/*! \file test-fp.cpp
** \verbatim
** Top contributors (to current version):
**   Augusto Mafra
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for theory of floating-point.
**
**
**/

#include <tuple>
#include <utility>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(FPTests);
class FPTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<tuple<SolverConfiguration, uint64_t>>
{
 protected:
  void SetUp() override
  {
    auto [sc, fp_size] = GetParam();
    s = create_solver(sc);
    s->set_opt("produce-models", "true");
    s->set_logic("QF_LRABVFP");

    auto [exp_size, sig_size] = get_fp_exp_and_sig(fp_size);
    float_sort = s->make_sort(FLOAT, exp_size, sig_size);
    rounding_mode = s->make_sort(ROUNDINGMODE);
  }

  static constexpr pair<uint64_t, uint64_t> get_fp_exp_and_sig(uint64_t fp_size)
  {
    switch (fp_size)
    {
      case 32: return { FPSizes<32>::exp, FPSizes<32>::sig };
      case 64: return { FPSizes<64>::exp, FPSizes<64>::sig };
      default:
        throw std::runtime_error("Unsupported FP size: " + to_string(fp_size));
    }
    return { FPSizes<64>::exp, FPSizes<64>::sig };
  }

  SmtSolver s;
  Sort float_sort;
  Sort rounding_mode;
};

TEST_P(FPTests, FPEq)
{
  Term x = s->make_symbol("x", float_sort);
  Term y = s->make_symbol("y", float_sort);
  Term z = s->make_symbol("z", float_sort);

  s->assert_formula(s->make_term(FPEq, x, y));
  s->assert_formula(s->make_term(FPEq, y, z));
  s->assert_formula(s->make_term(Not, s->make_term(FPEq, x, z)));

  Result res = s->check_sat();
  ASSERT_EQ(res, UNSAT);
}

TEST_P(FPTests, FPAbsNeg)
{
  Term x = s->make_symbol("x", float_sort);

  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsInf, x)));
  s->assert_formula(
      s->make_term(Not,
                   s->make_term(FPEq,
                                s->make_term(FPAbs, s->make_term(FPNeg, x)),
                                s->make_term(FPAbs, x))));

  Result res = s->check_sat();
  ASSERT_EQ(res, UNSAT);
}

TEST_P(FPTests, FPAdd)
{
  Term x = s->make_symbol("x", float_sort);
  Term y = s->make_symbol("y", float_sort);
  Term z = s->make_symbol("z", float_sort);
  Term rm = s->make_symbol("rm", rounding_mode);
  s->assert_formula(s->make_term(
      Not,
      s->make_term(FPEq,
                   s->make_term(FPAdd, rm, x, s->make_term(FPAdd, rm, y, z)),
                   s->make_term(FPAdd, rm, s->make_term(FPAdd, rm, x, y), z))));
  Result res = s->check_sat();
  ASSERT_EQ(res, SAT);
}

TEST_P(FPTests, FPSub)
{
  Term x = s->make_symbol("x", float_sort);
  Term zero = s->make_term("0.0", float_sort);
  Term rm = s->make_symbol("rm", rounding_mode);
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsInf, x)));
  s->assert_formula(s->make_term(
      Not, s->make_term(FPEq, s->make_term(FPSub, rm, x, x), zero)));
  Result res = s->check_sat();
  ASSERT_EQ(res, UNSAT);
}

TEST_P(FPTests, FPMul)
{
  Term x = s->make_symbol("x", float_sort);
  Term zero = s->make_term("0.0", float_sort);
  Term rm = s->make_symbol("rm", rounding_mode);
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsInf, x)));
  s->assert_formula(s->make_term(
      Not, s->make_term(FPEq, s->make_term(FPMul, rm, x, zero), zero)));
  Result res = s->check_sat();
  ASSERT_EQ(res, UNSAT);
}

TEST_P(FPTests, FPDiv)
{
  Term x = s->make_symbol("x", float_sort);
  Term zero = s->make_term("0.0", float_sort);
  Term rm = s->make_symbol("rm", rounding_mode);
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsInf, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPEq, x, zero)));
  s->assert_formula(s->make_term(
      Not, s->make_term(FPEq, s->make_term(FPDiv, rm, zero, x), zero)));
  Result res = s->check_sat();
  ASSERT_EQ(res, UNSAT);
}

TEST_P(FPTests, FPFma)
{
  Term x = s->make_symbol("x", float_sort);
  Term y = s->make_symbol("y", float_sort);
  Term z = s->make_symbol("z", float_sort);
  Term rm = s->make_symbol("rm", rounding_mode);
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsInf, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, y)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsInf, y)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, z)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsInf, z)));
  s->assert_formula(s->make_term(
      Not,
      s->make_term(FPEq,
                   s->make_term(FPFma, TermVec{ rm, x, y, z }),
                   s->make_term(FPAdd, rm, s->make_term(FPMul, rm, x, y), z))));
  Result res = s->check_sat();
  ASSERT_EQ(res, SAT);
}

TEST_P(FPTests, FPSqrt)
{
  Term zero = s->make_term("0.0", float_sort);
  Term rm = s->make_symbol("rm", rounding_mode);
  s->assert_formula(s->make_term(
      Not, s->make_term(FPEq, s->make_term(FPSqrt, rm, zero), zero)));
  Result res = s->check_sat();
  ASSERT_EQ(res, UNSAT);
}

TEST_P(FPTests, FPRem)
{
  Term x = s->make_symbol("x", float_sort);
  Term zero = s->make_term("0.0", float_sort);
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsInf, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPEq, x, zero)));
  s->assert_formula(
      s->make_term(Not, s->make_term(FPEq, s->make_term(FPRem, x, x), zero)));
  Result res = s->check_sat();
  ASSERT_EQ(res, UNSAT);
}

TEST_P(FPTests, FPRti)
{
  Term x = s->make_symbol("x", float_sort);
  Term frac = s->make_term("0.1", float_sort);
  Term minus_zero = s->make_term(FPSpecialValue::NEG_ZERO, float_sort);
  Term pos_zero = s->make_term(FPSpecialValue::POS_ZERO, float_sort);
  Term rm = s->make_symbol("rm", rounding_mode);
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsInf, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPEq, x, minus_zero)));
  s->assert_formula(s->make_term(Not, s->make_term(FPEq, x, pos_zero)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsSubNormal, x)));
  s->assert_formula(s->make_term(
      Not,
      s->make_term(FPEq,
                   s->make_term(FPRti, rm, (s->make_term(FPAdd, rm, x, frac))),
                   x)));
  Result res = s->check_sat();
  ASSERT_EQ(res, SAT);
}

TEST_P(FPTests, FPMin)
{
  Term x = s->make_symbol("x", float_sort);
  Term minus_inf = s->make_term(FPSpecialValue::NEG_INFINITY, float_sort);

  s->assert_formula(s->make_term(
      Not, s->make_term(FPEq, s->make_term(FPMin, x, minus_inf), minus_inf)));

  Result res = s->check_sat();
  ASSERT_EQ(res, UNSAT);
}

TEST_P(FPTests, FPMax)
{
  Term x = s->make_symbol("x", float_sort);
  Term plus_inf = s->make_term(FPSpecialValue::POS_INFINITY, float_sort);

  s->assert_formula(s->make_term(
      Not, s->make_term(FPEq, s->make_term(FPMax, x, plus_inf), plus_inf)));

  Result res = s->check_sat();
  ASSERT_EQ(res, UNSAT);
}

TEST_P(FPTests, FPLeq)
{
  Term x = s->make_symbol("x", float_sort);
  Term plus_inf = s->make_term(FPSpecialValue::POS_INFINITY, float_sort);
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPLeq, x, plus_inf)));

  Result res = s->check_sat();
  ASSERT_EQ(res, UNSAT);
}

TEST_P(FPTests, FPLt)
{
  Term x = s->make_symbol("x", float_sort);
  Term plus_inf = s->make_term(FPSpecialValue::POS_INFINITY, float_sort);
  s->assert_formula(s->make_term(Not, s->make_term(FPIsInf, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPLt, x, plus_inf)));

  Result res = s->check_sat();
  ASSERT_EQ(res, UNSAT);
}

TEST_P(FPTests, FPGeq)
{
  Term x = s->make_symbol("x", float_sort);
  Term minus_inf = s->make_term(FPSpecialValue::NEG_INFINITY, float_sort);
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPGeq, x, minus_inf)));

  Result res = s->check_sat();
  ASSERT_EQ(res, UNSAT);
}

TEST_P(FPTests, FPGt)
{
  Term x = s->make_symbol("x", float_sort);
  Term minus_inf = s->make_term(FPSpecialValue::NEG_INFINITY, float_sort);
  s->assert_formula(s->make_term(Not, s->make_term(FPIsInf, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPGt, x, minus_inf)));

  Result res = s->check_sat();
  ASSERT_EQ(res, UNSAT);
}

TEST_P(FPTests, FPPredicates)
{
  Term x = s->make_symbol("x", float_sort);
  s->assert_formula(s->make_term(FPIsNormal, x));
  s->assert_formula(s->make_term(FPIsPos, x));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsSubNormal, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsZero, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsInf, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNan, x)));
  s->assert_formula(s->make_term(Not, s->make_term(FPIsNeg, x)));
  Result res = s->check_sat();
  ASSERT_EQ(res, SAT);
}

TEST_P(FPTests, FPConversions)
{
  auto [_, fp_size] = GetParam();
  auto [exp_size, sig_size] = get_fp_exp_and_sig(fp_size);
  auto [other_exp_size, other_sig_size] =
      get_fp_exp_and_sig(fp_size == 32 ? 64 : 32);
  Sort bv_sort = s->make_sort(BV, fp_size);
  Sort other_float_sort = s->make_sort(FLOAT, other_exp_size, other_sig_size);
  Sort real = s->make_sort(REAL);

  Term bv = s->make_symbol("bv", bv_sort);
  Term r = s->make_symbol("r", real);
  Term x = s->make_symbol("x", float_sort);
  Term y = s->make_symbol("y", other_float_sort);
  Term rm = s->make_symbol("rm", rounding_mode);

  s->assert_formula(s->make_term(
      FPEq, s->make_term(Op{ IEEEBV_To_FP, exp_size, sig_size }, bv), x));
  s->assert_formula(s->make_term(
      FPEq, s->make_term(Op{ FP_To_FP, exp_size, sig_size }, rm, y), x));
  s->assert_formula(s->make_term(
      FPEq, s->make_term(Op{ Real_To_FP, exp_size, sig_size }, rm, r), x));
  s->assert_formula(s->make_term(Equal, s->make_term(FP_To_REAL, x), r));

  Result res = s->check_sat();
  ASSERT_EQ(res, SAT);
}

TEST_P(FPTests, FPSBVConversions)
{
  auto [_, fp_size] = GetParam();
  auto [exp_size, sig_size] = get_fp_exp_and_sig(fp_size);
  Sort bv_sort = s->make_sort(BV, fp_size);

  Term rm = s->make_symbol("rm", rounding_mode);
  Term bv = s->make_symbol("bv", bv_sort);

  s->assert_formula(s->make_term(
      Not,
      s->make_term(
          Equal,
          s->make_term(
              Op{ FP_To_SBV, fp_size },
              rm,
              s->make_term(Op{ SBV_To_FP, exp_size, sig_size }, rm, bv)),
          bv)));

  Result res = s->check_sat();
  ASSERT_EQ(res, SAT);
}

TEST_P(FPTests, FPUBVConversions)
{
  auto [_, fp_size] = GetParam();
  auto [exp_size, sig_size] = get_fp_exp_and_sig(fp_size);
  Sort bv_sort = s->make_sort(BV, fp_size);

  Term rm = s->make_symbol("rm", rounding_mode);
  Term bv = s->make_symbol("bv", bv_sort);

  s->assert_formula(s->make_term(
      Not,
      s->make_term(
          Equal,
          s->make_term(
              Op{ FP_To_UBV, fp_size },
              rm,
              s->make_term(Op{ UBV_To_FP, exp_size, sig_size }, rm, bv)),
          bv)));

  Result res = s->check_sat();
  ASSERT_EQ(res, SAT);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverFPTests,
    FPTests,
    testing::Combine(testing::ValuesIn(filter_non_logging_solver_configurations(
                         { THEORY_FP })),
                     testing::Values(32, 64)));

}  // namespace smt_tests
