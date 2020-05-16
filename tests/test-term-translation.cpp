#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"
#include "test-utils.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class SelfTranslationTests : public ::testing::Test,
                             public ::testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    bvsort8 = s->make_sort(BV, 8);

    x = s->make_symbol("x", bvsort8);
    y = s->make_symbol("y", bvsort8);
    z = s->make_symbol("z", bvsort8);
  }
  SmtSolver s;
  Sort bvsort8;
  Term x, y, z;
};

class SelfTranslationIntTests : public ::testing::Test,
                                public ::testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    intsort = s->make_sort(INT);

    x = s->make_symbol("x", intsort);
    y = s->make_symbol("y", intsort);
    z = s->make_symbol("z", intsort);
  }
  SmtSolver s;
  Sort intsort;
  Term x, y, z;
};

TEST_P(SelfTranslationTests, BVTransfer)
{
  SmtSolver s2 = create_solver(GetParam());
  TermTranslator tt(s2);
  Term constraint = s->make_term(Equal, z, s->make_term(BVAdd, x, y));
  Term T = s->make_term(true);
  Term two = s->make_term(2, bvsort8);

  Term constraint2 = tt.transfer_term(constraint);
  Term T2 = tt.transfer_term(T);
  ASSERT_EQ(T2, s2->make_term(true));
  Term two_2 = tt.transfer_term(two);
  ASSERT_EQ(two_2, s2->make_term(2, bvsort8));
  // ensure it can handle transfering again (even though it already built the
  // node)
  Term cached_constraint2 = constraint2;
  constraint2 = tt.transfer_term(constraint);
  ASSERT_EQ(cached_constraint2, constraint2);
  s2->assert_formula(constraint2);

  ASSERT_TRUE(s->check_sat().is_sat());
  ASSERT_TRUE(s2->check_sat().is_sat());
}

TEST_P(SelfTranslationIntTests, IntTransfer)
{
  SmtSolver s2 = create_solver(GetParam());
  TermTranslator tt(s2);

  Term xpy = s->make_term(Plus, x, y);
  Term xpymz = s->make_term(Minus, xpy, z);

  Term xpymz_transfer = tt.transfer_term(xpymz);
  // recover symbols
  unordered_map<string, Term> s2_symbols;
  for (auto sym : get_free_symbols(xpymz_transfer))
  {
    s2_symbols[sym->to_string()] = sym;
  }
  Term xpymz_2 =
      s2->make_term(Minus,
                    s2->make_term(Plus, s2_symbols.at("x"), s2_symbols.at("y")),
                    s2_symbols.at("z"));
  ASSERT_EQ(xpymz_transfer, xpymz_2);
  // test that you can retransfer
  xpymz_transfer = tt.transfer_term(xpymz);
  ASSERT_EQ(xpymz_transfer, xpymz_2);

  Term two = s->make_term(2, intsort);
  Term neg_two = s->make_term(Negate, two);
  Term xp2 = s->make_term(Plus, x, two);

  Term two_transfer = tt.transfer_term(two);
  Term two_2 = s2->make_term(2, intsort);
  ASSERT_EQ(two_transfer, two_2);

  Term neg_two_transfer = tt.transfer_term(neg_two);
  Term neg_two_2 = s2->make_term(Negate, two_2);
  ASSERT_EQ(neg_two_transfer, neg_two_2);

  Term xp2_transfer = tt.transfer_term(xp2);
  Term xp2_2 = s2->make_term(Plus, s2_symbols.at("x"), two_2);
  ASSERT_EQ(xp2_transfer, xp2_2);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSelfTranslationTests,
                         SelfTranslationTests,
                         testing::ValuesIn(filter_solver_enums({ TERMITER })));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSelfTranslationIntTests,
    SelfTranslationIntTests,
    testing::ValuesIn(filter_solver_enums({ FULL_TRANSFER, THEORY_INT })));

}  // namespace smt_tests
