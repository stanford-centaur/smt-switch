#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "bitwuzla_factory.h"
#include "exec_utils.h"
#include "printing_solver.h"
#include "smt.h"
#include "utils.h"

using namespace smt;

namespace smt_tests {

class BitwuzlaPrintingTest : public testing::Test
{
 protected:
  void SetUp() override { os = new std::ostream(&strbuf); }
  void TearDown() override { delete os; }
  void check_result(
      std::vector<std::unordered_set<std::string>> expected_results,
      std::string extra_opts = "")
  {
#ifdef BITWUZLA_BINARY
    dump_and_run(BITWUZLA_BINARY, strbuf, expected_results, extra_opts);
#else
    GTEST_SKIP() << "configure found no bitwuzla executable";
#endif
  }
  std::stringbuf strbuf;
  std::ostream * os;
};

TEST_F(BitwuzlaPrintingTest, Interpolation)
{
  SmtInterpolator solver = create_printing_interpolator(
      BitwuzlaSolverFactory::create_interpolating_solver(),
      os,
      PrintingStyleEnum::BZLA_STYLE);
  solver->set_logic("QF_BV");
  solver->set_opt("interpolants-subst", "true");
  Sort bvsort = solver->make_sort(BV, 2);

  Term x = solver->make_symbol("x", bvsort);
  Term y = solver->make_symbol("y", bvsort);
  Term z = solver->make_symbol("z", bvsort);

  // x<y /\ y<z
  Term A = solver->make_term(
      And, solver->make_term(BVUlt, x, y), solver->make_term(BVUlt, y, z));
  // x<z
  Term B = solver->make_term(BVUgt, x, z);
  Term I;
  solver->get_interpolant(A, B, I);

  // z<y /\ y<x
  Term A1 = solver->make_term(
      And, solver->make_term(BVUlt, z, y), solver->make_term(BVUlt, y, x));
  // z<x
  Term B1 = solver->make_term(BVUgt, z, x);
  Term I1;
  solver->get_interpolant(A1, B1, I1);

  check_result({ { "unsat" },
                 { "(not (bvult z x))" },
                 { "unsat" },
                 { "(not (bvult x z))" } },
               "--produce-interpolants");
}

TEST_F(BitwuzlaPrintingTest, SequenceInterpolation)
{
  SmtInterpolator solver = create_printing_interpolator(
      BitwuzlaSolverFactory::create_interpolating_solver(),
      os,
      PrintingStyleEnum::BZLA_STYLE);
  solver->set_logic("QF_BV");
  solver->set_opt("interpolants-subst", "true");
  Sort bvsort = solver->make_sort(BV, 2);
  Term x = solver->make_symbol("x", bvsort);
  Term y = solver->make_symbol("y", bvsort);
  Term z = solver->make_symbol("z", bvsort);

  // x < y, y < z and z < x cannot all hold
  TermVec formulae = { solver->make_term(BVUlt, x, y),
                       solver->make_term(BVUlt, y, z),
                       solver->make_term(BVUlt, z, x) };
  TermVec interpolants;
  ASSERT_TRUE(
      solver->get_sequence_interpolants(formulae, interpolants).is_unsat());
  EXPECT_EQ(interpolants.size(), 2);

  check_result({ { "unsat" },
                 { "(" },
                 { "(bvult x y)" },
                 { "(and (not (and (= ((_ extract 1 1) z) #b0) (= #b1 ((_ "
                   "extract 1 1) x)))) (not (and (= ((_ extract 0 0) z) #b0) "
                   "(= #b1 ((_ extract 0 0) x)))))" },
                 { ")" } },
               "--produce-interpolants");
}

}  // namespace smt_tests
