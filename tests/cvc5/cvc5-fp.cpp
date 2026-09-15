/*********************                                                        */
/*! \file cvc5-fp.cpp
** \verbatim
** Top contributors (to current version):
**   Augusto Mafra
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
** Tests for floating-point in the cvc5 backend.
**/

#include "assert.h"
#include "cvc5_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = Cvc5SolverFactory::create(false);
  s->set_opt("produce-models", "true");
  s->set_logic("QF_FP");
  Sort float32 = s->make_sort(FLOAT, FPSizes<32>::exp, FPSizes<32>::sig);
  Sort float64 = s->make_sort(FLOAT, FPSizes<64>::exp, FPSizes<64>::sig);
  Sort rounding_mode = s->make_sort(ROUNDINGMODE);

  Term x64 = s->make_symbol("x64", float64);
  Term x32 = s->make_symbol("x32", float32);
  Term rm = s->make_symbol("rm", rounding_mode);

  Term rne = s->make_term(FPRoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
  Term rnp = s->make_term(FPRoundingMode::ROUND_TOWARD_POSITIVE);
  Term rnn = s->make_term(FPRoundingMode::ROUND_TOWARD_NEGATIVE);
  Term rnz = s->make_term(FPRoundingMode::ROUND_TOWARD_ZERO);
  Term rna = s->make_term(FPRoundingMode::ROUND_NEAREST_TIES_TO_AWAY);

  Term plus_inf64 = s->make_term(FPSpecialValue::POS_INFINITY, float64);
  Term minus_inf64 = s->make_term(FPSpecialValue::NEG_INFINITY, float64);
  Term nan64 = s->make_term(FPSpecialValue::NOT_A_NUMBER, float64);
  Term plus_zero64 = s->make_term(FPSpecialValue::POS_ZERO, float64);
  Term minus_zero64 = s->make_term(FPSpecialValue::NEG_ZERO, float64);
  Term plus_inf32 = s->make_term(FPSpecialValue::POS_INFINITY, float32);
  Term minus_inf32 = s->make_term(FPSpecialValue::NEG_INFINITY, float32);
  Term nan32 = s->make_term(FPSpecialValue::NOT_A_NUMBER, float32);
  Term plus_zero32 = s->make_term(FPSpecialValue::POS_ZERO, float32);
  Term minus_zero32 = s->make_term(FPSpecialValue::NEG_ZERO, float32);

  s->assert_formula(
      s->make_term(FPEq, s->make_term(FPAdd, rm, x64, plus_inf64), plus_inf64));
  s->assert_formula(s->make_term(
      FPEq, s->make_term(FPAdd, rne, x32, plus_inf32), plus_inf32));

  s->assert_formula(
      s->make_term(FPEq, s->make_term(FPSub, rnp, nan64, x64), nan64));
  s->assert_formula(
      s->make_term(FPEq, s->make_term(FPSub, rnn, nan32, x32), nan32));

  s->assert_formula(s->make_term(
      FPEq, s->make_term(FPMul, rnz, x64, minus_inf64), minus_inf64));
  s->assert_formula(s->make_term(
      FPEq, s->make_term(FPMul, rna, x32, minus_inf32), minus_inf32));

  s->assert_formula(s->make_term(
      FPEq, s->make_term(FPDiv, rm, plus_zero64, x64), plus_zero64));
  s->assert_formula(s->make_term(
      FPEq, s->make_term(FPDiv, rm, plus_zero32, x32), plus_zero32));

  s->assert_formula(
      s->make_term(FPEq, s->make_term(FPRem, minus_zero64, x64), minus_zero64));
  s->assert_formula(
      s->make_term(FPEq, s->make_term(FPRem, minus_zero32, x32), minus_zero32));

  Result res = s->check_sat();
  assert(res.is_unsat());

  return 0;
}
