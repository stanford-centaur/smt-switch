/*********************                                                        */
/*! \file msat-printing.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
**
**
**/
#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "exec_utils.h"
#include "msat_factory.h"
#include "printing_solver.h"
#include "smt.h"
#include "utils.h"

using namespace smt;

namespace smt_tests {

class MsatPrintingTest : public testing::Test
{
 protected:
  void SetUp() override { os = new std::ostream(&strbuf); }
  void TearDown() override { delete os; }
  void check_result(
      std::vector<std::unordered_set<std::string>> expected_result,
      std::string extra_opts = "")
  {
#ifdef MATHSAT_BINARY
    dump_and_run(MATHSAT_BINARY, strbuf, expected_result, extra_opts);
#else
    GTEST_SKIP() << "configure found no mathsat executable";
#endif
  }
  std::stringbuf strbuf;
  std::ostream * os;
};

TEST_F(MsatPrintingTest, Interpolation)
{
  SmtInterpolator s = create_printing_interpolator(
      MsatSolverFactory::create_interpolating_solver(),
      os,
      PrintingStyleEnum::MSAT_STYLE);
  s->set_logic("QF_LIA");

  Sort intsort = s->make_sort(INT);

  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  Term B = s->make_term(Gt, x, z);
  Term I;
  Result r = s->get_interpolant(A, B, I);
  ASSERT_TRUE(r.is_unsat());

  Term A1 = s->make_term(And, s->make_term(Lt, z, y), s->make_term(Lt, y, x));
  Term B1 = s->make_term(Gt, z, x);
  Term I1;
  Result r1 = s->get_interpolant(A1, B1, I1);
  ASSERT_TRUE(r1.is_unsat());

  check_result(
      {
          { "unsat" },
          { "(<= 2 (+ z (* (- 1) x)))", "(<= (+ x (* (- 1) z)) (- 2))" },
          { "unsat" },
          { "(<= 2 (+ x (* (- 1) z)))", "(<= (+ z (* (- 1) x)) (- 2))" },
      },
      "-interpolation=true");
}

TEST_F(MsatPrintingTest, SequenceInterpolation)
{
  SmtInterpolator s = create_printing_interpolator(
      MsatSolverFactory::create_interpolating_solver(),
      os,
      PrintingStyleEnum::MSAT_STYLE);
  s->set_logic("QF_LIA");
  Sort intsort = s->make_sort(INT);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  // x < y, y < z and z < x cannot all hold
  TermVec formulae = { s->make_term(Lt, x, y),
                       s->make_term(Lt, y, z),
                       s->make_term(Lt, z, x) };
  TermVec interpolants;
  ASSERT_TRUE(s->get_sequence_interpolants(formulae, interpolants).is_unsat());
  EXPECT_EQ(interpolants.size(), 2);

  check_result(
      {
          { "unsat" },
          { "(<= 1 (+ y (* (- 1) x)))", "(<= (+ x (* (- 1) y)) (- 1))" },
          { "(<= 2 (+ z (* (- 1) x)))", "(<= (+ x (* (- 1) z)) (- 2))" },
      },
      "-interpolation=true");
}

}  // namespace smt_tests
