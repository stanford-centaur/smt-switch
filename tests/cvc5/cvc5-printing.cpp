/*!
 * \file cvc5-printing.cpp
 * \brief Tests that printed cvc5 interpolation queries replay
 * \author Yoni Zohar
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <memory>
#include <ostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "exec_utils.h"
#include "smt-switch/cvc5_factory.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/interpolator.h"
#include "smt-switch/ops.h"
#include "smt-switch/printing_interpolator.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "test_paths.h"

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
    if (smt_tests::cvc5_binary.empty())
    {
      GTEST_SKIP() << "configure found no cvc5 executable";
    }
    dump_and_run(smt_tests::cvc5_binary, strbuf, expected_result, extra_opts);
  }
  std::stringbuf strbuf;
  std::ostream * os;
};

TEST_F(Cvc5PrintingTest, Interpolation)
{
  SmtInterpolator s = create_printing_interpolator(
      Cvc5SolverFactory::create_interpolator(), os);
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

  // x=0
  EXPECT_THROW(
      s->assert_formula(s->make_term(Equal, x, s->make_term(0, intsort))),
      IncorrectUsageException);

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
      Cvc5SolverFactory::create_interpolator(), os);
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
      Cvc5SolverFactory::create_interpolator(), os);
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
      Cvc5SolverFactory::create_interpolator(), os);
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
