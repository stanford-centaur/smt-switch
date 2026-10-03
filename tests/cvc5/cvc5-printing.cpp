/*********************                                                        */
/*! \file cvc5-printinh.cpp
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

#include "cvc5_factory.h"
#include "exec_utils.h"
#include "printing_solver.h"
#include "smt.h"
#include "utils.h"

using namespace smt;

namespace smt_tests {

class Cvc5PrintingTest : public testing::Test
{
 protected:
  void SetUp() override { os = new std::ostream(&strbuf); }
  void TearDown() override { delete os; }
  void check_result(
      std::vector<std::unordered_set<std::string>> expected_result,
      std::string extra_opts = "")
  {
#ifdef CVC5_BINARY
    dump_and_run(CVC5_BINARY, strbuf, expected_result, extra_opts);
#else
    GTEST_SKIP() << "configure found no cvc5 executable";
#endif
  }
  std::stringbuf strbuf;
  std::ostream * os;
};

TEST_F(Cvc5PrintingTest, Interpolation)
{
  SmtInterpolator s = create_printing_interpolator(
      Cvc5SolverFactory::create_interpolating_solver(),
      os,
      PrintingStyleEnum::CVC5_STYLE);
  s->set_logic("QF_LIA");
  s->set_opt("bv-print-consts-as-indexed-symbols", "true");
  Sort intsort = s->make_sort(INT);

  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  // x<y /\ y<z
  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  // x<z
  Term B = s->make_term(Gt, x, z);
  Term I;
  s->get_interpolant(A, B, I);

  // z<y /\ y<x
  Term A1 = s->make_term(And, s->make_term(Lt, z, y), s->make_term(Lt, y, x));
  // z<x
  Term B1 = s->make_term(Gt, z, x);
  Term I1;
  s->get_interpolant(A1, B1, I1);

  try
  {
    // x=0
    s->assert_formula(s->make_term(Equal, x, s->make_term(0, intsort)));
  }
  catch (IncorrectUsageException & e)
  {
    std::cout << e.what() << std::endl;
  }

  check_result(
      {
          { "(define-fun I () Bool (<= x z))" },
          { "(define-fun I () Bool (<= z x))" },
      },
      "--produce-interpolants --incremental");
}

}  // namespace smt_tests
