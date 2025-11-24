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

#include <cassert>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "cvc5_factory.h"
#include "printing_solver.h"
#include "smt.h"
#include "test-utils.h"

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
    dump_and_run(CVC5, strbuf, expected_result, extra_opts);
  }
  std::stringbuf strbuf;
  std::ostream * os;
};

TEST_F(Cvc5PrintingTest, Interpolation)
{
  SmtSolver s =
      create_printing_solver(Cvc5SolverFactory::create_interpolating_solver(),
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

TEST_F(Cvc5PrintingTest, Solving)
{
  SmtSolver s = create_printing_solver(
      Cvc5SolverFactory::create(false), os, PrintingStyleEnum::CVC5_STYLE);
  s->set_logic("QF_AUFBV");
  s->set_opt("produce-models", "true");
  s->set_opt("produce-unsat-assumptions", "true");
  s->set_opt("incremental", "true");
  s->set_opt("bv-print-consts-as-indexed-symbols", "true");
  Sort us = s->make_sort("S", 0);
  Sort bvsort32 = s->make_sort(BV, 32);
  Sort fun_sort = s->make_sort(FUNCTION, SortVec{ bvsort32, us });
  Sort array32_32 = s->make_sort(ARRAY, bvsort32, bvsort32);
  Term x = s->make_symbol("x", bvsort32);
  Term y = s->make_symbol("y", bvsort32);
  Term arr = s->make_symbol("arr", array32_32);
  Term fun = s->make_symbol("f", fun_sort);

  Term S0 = s->make_symbol("s", us);

  Term ind1 = s->make_symbol("ind1", s->make_sort(BOOL));
  Term f = s->make_term(Equal, s->make_term(Apply, fun, x), S0);
  s->push(1);
  s->assert_formula(ind1);
  s->assert_formula(s->make_term(Equal, ind1, f));
  s->assert_formula(f);
  s->assert_formula(
      s->make_term(Not,
                   s->make_term(Implies,
                                s->make_term(Equal, x, y),
                                s->make_term(Equal,
                                             s->make_term(Select, arr, x),
                                             s->make_term(Select, arr, y)))));
  Result r = s->check_sat_assuming(TermVec{ ind1 });
  assert(r.is_unsat());
  UnorderedTermSet usc;
  s->get_unsat_assumptions(usc);
  s->pop(1);
  s->check_sat();
  s->get_value(x);
  check_result({
      { "unsat" },
      { "(ind1)" },
      { "sat" },
      { "((x (_ bv0 32)))" },
  });
}

}  // namespace smt_tests
