#include <gtest/gtest.h>

#include <memory>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "exec_utils.h"
#include "smt-switch/bitwuzla_factory.h"
#include "smt-switch/interpolating_solver.h"
#include "smt-switch/ops.h"
#include "smt-switch/printing_solver.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "test_paths.h"

using namespace smt;
using namespace smt_tests;

namespace {

class BitwuzlaPrintingTest : public testing::Test
{
 protected:
  void SetUp() override
  {
#ifndef SMT_SWITCH_BITWUZLA_HAS_INTERPOLANTS
    GTEST_SKIP() << "this Bitwuzla cannot interpolate";
#endif
    os = new std::ostream(&strbuf);
  }
  void TearDown() override { delete os; }
  void check_result(
      std::vector<std::unordered_set<std::string>> expected_results,
      std::string extra_opts = "")
  {
    if (smt_tests::bitwuzla_binary.empty())
    {
      GTEST_SKIP() << "configure found no bitwuzla executable";
    }
    dump_and_run(
        smt_tests::bitwuzla_binary, strbuf, expected_results, extra_opts);
  }
  std::stringbuf strbuf;
  std::ostream * os = nullptr;
};

TEST_F(BitwuzlaPrintingTest, Interpolation)
{
  SmtInterpolator solver = create_printing_interpolator(
      BitwuzlaSolverFactory::create_interpolating_solver(), os);
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

  // each is asked as a sequence of two, as the interpolator runs it
  check_result({ { "unsat" },
                 { "(" },
                 { "(not (bvult z x))" },
                 { ")" },
                 { "unsat" },
                 { "(" },
                 { "(not (bvult x z))" },
                 { ")" } },
               "--produce-interpolants");
}

TEST_F(BitwuzlaPrintingTest, SequenceInterpolation)
{
  SmtInterpolator solver = create_printing_interpolator(
      BitwuzlaSolverFactory::create_interpolating_solver(), os);
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

// a query that extends the last one keeps its formulas asserted, and one
// that shares only a prefix with it, or nothing, pops the rest
TEST_F(BitwuzlaPrintingTest, ReusedSequenceInterpolation)
{
  SmtInterpolator solver = create_printing_interpolator(
      BitwuzlaSolverFactory::create_interpolating_solver(), os);
  solver->set_logic("QF_BV");
  solver->set_opt("interpolants-subst", "true");
  Sort bvsort = solver->make_sort(BV, 2);
  Term x = solver->make_symbol("x", bvsort);
  Term y = solver->make_symbol("y", bvsort);
  Term z = solver->make_symbol("z", bvsort);
  Term xy = solver->make_term(BVUlt, x, y);
  Term yz = solver->make_term(BVUlt, y, z);
  Term zx = solver->make_term(BVUlt, z, x);
  Term xz = solver->make_term(BVUlt, x, z);
  for (const TermVec & formulae : { TermVec{ xy, yz, zx },
                                    TermVec{ xy, yz, zx, xz },
                                    TermVec{ xy, zx, yz },
                                    TermVec{ yz, zx, xy } })
  {
    TermVec interpolants;
    ASSERT_TRUE(
        solver->get_sequence_interpolants(formulae, interpolants).is_unsat());
  }

  const std::string x_lt_z_bits =
      "(and (not (and (= ((_ extract 1 1) z) #b0) (= #b1 ((_ extract 1 1) "
      "x)))) (not (and (= ((_ extract 0 0) z) #b0) (= #b1 ((_ extract 0 0) "
      "x)))))";
  check_result(
      { { "unsat" },
        { "(" },
        { "(bvult x y)" },
        { x_lt_z_bits },
        { ")" },
        { "unsat" },
        { "(" },
        { "(bvult x y)" },
        { x_lt_z_bits },
        { "(and (not (and (= ((_ extract 0 0) z) #b0) (= #b1 ((_ extract 0 0) "
          "x)))) (and (bvult z x) (not (and (= ((_ extract 1 1) z) #b0) (= "
          "#b1 ((_ extract 1 1) x))))))" },
        { ")" },
        { "unsat" },
        { "(" },
        { "(bvult x y)" },
        { "(and (not (and (= ((_ extract 1 1) z) #b1) (= ((_ extract 1 1) y) "
          "#b0))) (not (and (= #b1 ((_ extract 0 0) z)) (= ((_ extract 0 0) "
          "y) #b0))))",
          "(not (and (not (and (= ((_ extract 0 0) z) #b0) (= #b1 ((_ extract "
          "1 1) y)))) (not (and (= ((_ extract 1 1) z) #b0) (= #b1 ((_ "
          "extract 0 0) y))))))" },
        { ")" },
        { "unsat" },
        { "(" },
        { "(bvult y z)" },
        { "(and (not (and (= ((_ extract 1 1) x) #b0) (= #b1 ((_ extract 1 1) "
          "y)))) (not (and (= ((_ extract 0 0) x) #b0) (= #b1 ((_ extract 0 0) "
          "y)))))",
          "(not (and (not (and (= ((_ extract 0 0) x) #b1) (= ((_ extract 1 1) "
          "y) #b0))) (not (and (= #b1 ((_ extract 1 1) x)) (= ((_ extract 0 0) "
          "y) #b0)))))" },
        { ")" } },
      "--produce-interpolants");
}

// copies share the wrapped interpolator, so a query through one pops what a
// query through the other left asserted
TEST_F(BitwuzlaPrintingTest, CopiesShareWhatIsAsserted)
{
  SmtInterpolator solver = create_printing_interpolator(
      BitwuzlaSolverFactory::create_interpolating_solver(), os);
  auto copy = std::make_shared<PrintingInterpolator>(
      *std::static_pointer_cast<PrintingInterpolator>(solver));
  solver->set_logic("QF_BV");
  Sort bvsort = solver->make_sort(BV, 2);
  Term x = solver->make_symbol("x", bvsort);
  Term y = solver->make_symbol("y", bvsort);
  Term z = solver->make_symbol("z", bvsort);
  Term xy = solver->make_term(BVUlt, x, y);
  Term yz = solver->make_term(BVUlt, y, z);
  Term zx = solver->make_term(BVUlt, z, x);

  TermVec first;
  ASSERT_TRUE(
      solver->get_sequence_interpolants({ xy, yz, zx }, first).is_unsat());
  TermVec second;
  ASSERT_TRUE(
      copy->get_sequence_interpolants({ yz, zx, xy }, second).is_unsat());
  EXPECT_NE(strbuf.str().find("(pop 3)"), std::string::npos);
}

}  // namespace
