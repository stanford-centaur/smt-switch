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
#include "exceptions.h"
#include "exec_utils.h"
#include "interpolating_solver.h"
#include "ops.h"
#include "printing_solver.h"
#include "result.h"
#include "smt_defs.h"
#include "sort.h"
#include "term.h"
#include "utils.h"

using namespace smt;
using namespace smt_tests;

namespace {

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
      Cvc5SolverFactory::create_interpolating_solver(), os);
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

TEST_F(Cvc5PrintingTest, SequenceInterpolation)
{
  SmtInterpolator s = create_printing_interpolator(
      Cvc5SolverFactory::create_interpolating_solver(), os);
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

  // the second split asserts the first interpolant, which brings in x
  check_result({ { "(define-fun I () Bool (<= x y))" },
                 { "(define-fun I () Bool (<= x z))" } },
               "--produce-interpolants --incremental");
}

// a query that extends an unsat last one asks only its new splits
TEST_F(Cvc5PrintingTest, ReusedSequenceInterpolation)
{
  SmtInterpolator s = create_printing_interpolator(
      Cvc5SolverFactory::create_interpolating_solver(), os);
  s->set_logic("QF_LIA");
  Sort intsort = s->make_sort(INT);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);
  Term xy = s->make_term(Lt, x, y);
  Term yz = s->make_term(Lt, y, z);
  Term zx = s->make_term(Lt, z, x);
  Term xz = s->make_term(Lt, x, z);
  for (const TermVec & formulae : { TermVec{ xy, yz, zx },
                                    TermVec{ xy, yz, zx, xz },
                                    TermVec{ xy, zx, yz },
                                    TermVec{ yz, zx, xy } })
  {
    TermVec interpolants;
    ASSERT_TRUE(
        s->get_sequence_interpolants(formulae, interpolants).is_unsat());
  }

  // the second query asks only its last split, from the reused (<= x z)
  check_result({ { "(define-fun I () Bool (<= x y))" },
                 { "(define-fun I () Bool (<= x z))" },
                 { "(define-fun I () Bool false)" },
                 { "(define-fun I () Bool (<= x y))" },
                 { "(define-fun I () Bool (<= z y))" },
                 { "(define-fun I () Bool (<= y z))" },
                 { "(define-fun I () Bool (<= y x))" } },
               "--produce-interpolants --incremental");
}

// get_interpolant asks its pair on its own, so a sequence query that
// extends that pair asks every split
TEST_F(Cvc5PrintingTest, SequenceInterpolationAfterInterpolant)
{
  SmtInterpolator s = create_printing_interpolator(
      Cvc5SolverFactory::create_interpolating_solver(), os);
  s->set_logic("QF_LIA");
  Sort intsort = s->make_sort(INT);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);
  Term xy = s->make_term(Lt, x, y);
  Term yzx = s->make_term(And, s->make_term(Lt, y, z), s->make_term(Lt, z, x));
  Term I;
  ASSERT_TRUE(s->get_interpolant(xy, yzx, I).is_unsat());
  TermVec interpolants;
  ASSERT_TRUE(s->get_sequence_interpolants({ xy, yzx, s->make_term(Lt, x, z) },
                                           interpolants)
                  .is_unsat());

  // the rest after the first split is unsat on its own
  check_result({ { "(define-fun I () Bool (<= x y))" },
                 { "(define-fun I () Bool true)" },
                 { "(define-fun I () Bool (<= z x))" } },
               "--produce-interpolants --incremental");
}

}  // namespace
