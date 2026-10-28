/*********************                                                        */
/*! \file yices2-gtest.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
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

#include <string>
#include <utility>
#include <vector>

#include "exceptions.h"
#include "gtest/gtest.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"
#include "yices2_factory.h"

using namespace smt;
using namespace std;

namespace {

class Yices2Pow : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    s = Yices2SolverFactory::create(true);
    int_sort = s->make_sort(INT);
    a = s->make_symbol("a", int_sort);
    b = s->make_symbol("b", int_sort);
  }
  SmtSolver s;
  Sort int_sort;
  Term a, b;
};

TEST_F(Yices2Pow, RefusesExponentAboveUint32)
{
  // 2^32 + 2, which a 32-bit truncation would read as 2
  Term exponent = s->make_term("4294967298", int_sort);
  EXPECT_THROW(s->make_term(Pow, a, exponent), NotImplementedException);
}
TEST_F(Yices2Pow, RefusesNegativeExponent)
{
  Term exponent = s->make_term("-1", int_sort);
  EXPECT_THROW(s->make_term(Pow, a, exponent), NotImplementedException);
}
TEST_F(Yices2Pow, RefusesSymbolicExponent)
{
  EXPECT_THROW(s->make_term(Pow, a, b), NotImplementedException);
}

// Unwrapped, as the logging solver would work out the sort itself
TEST(Yices2IntToBv, FoldsValueModuloWidth)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort intsort = s->make_sort(INT);
  Sort bvsort8 = s->make_sort(BV, 8);
  Op int_to_bv8(Int_To_BV, 8);

  Term five = s->make_term(int_to_bv8, s->make_term("5", intsort));
  EXPECT_EQ(five->get_sort(), bvsort8);
  EXPECT_EQ(five, s->make_term(5, bvsort8));
  EXPECT_EQ(s->make_term(int_to_bv8, s->make_term("-1", intsort)),
            s->make_term(255, bvsort8));
  // 2^70 + 3
  EXPECT_EQ(
      s->make_term(int_to_bv8, s->make_term("1180591620717411303427", intsort)),
      s->make_term(3, bvsort8));
  EXPECT_EQ(s->make_term(Op(Int_To_BV, 100), s->make_term("-1", intsort)),
            s->make_term(std::string(100, '1'), s->make_sort(BV, 100), 2));
}

TEST(Yices2IntToBv, RefusesSymbol)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Term a = s->make_symbol("a", s->make_sort(INT));
  EXPECT_THROW(s->make_term(Op(Int_To_BV, 8), a), NotImplementedException);
}

TEST(Yices2IntToBv, RefusesNonInteger)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Term r = s->make_symbol("r", s->make_sort(REAL));
  Term x = s->make_symbol("x", s->make_sort(BV, 8));
  EXPECT_THROW(s->make_term(Op(Int_To_BV, 8), r), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Op(Int_To_BV, 8), x), IncorrectUsageException);
}

// Unwrapped, as the logging solver would work out the sort itself
TEST(Yices2BvToInt, FoldsValue)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort intsort = s->make_sort(INT);
  Sort bvsort8 = s->make_sort(BV, 8);
  Term ff = s->make_term(255, bvsort8);

  Term unsigned_ff = s->make_term(UBV_To_Int, ff);
  EXPECT_EQ(unsigned_ff->get_sort(), intsort);
  EXPECT_EQ(unsigned_ff, s->make_term("255", intsort));
  EXPECT_EQ(s->make_term(BV_To_Nat, ff), s->make_term("255", intsort));
  EXPECT_EQ(s->make_term(SBV_To_Int, ff), s->make_term("-1", intsort));
  EXPECT_EQ(s->make_term(SBV_To_Int, s->make_term(127, bvsort8)),
            s->make_term("127", intsort));

  Term ones100 = s->make_term(std::string(100, '1'), s->make_sort(BV, 100), 2);
  EXPECT_EQ(s->make_term(UBV_To_Int, ones100),
            s->make_term("1267650600228229401496703205375", intsort));
  EXPECT_EQ(s->make_term(SBV_To_Int, ones100), s->make_term("-1", intsort));
}

TEST(Yices2BvToInt, RefusesSymbol)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Term x = s->make_symbol("x", s->make_sort(BV, 8));
  EXPECT_THROW(s->make_term(UBV_To_Int, x), NotImplementedException);
  EXPECT_THROW(s->make_term(SBV_To_Int, x), NotImplementedException);
}

TEST(Yices2BvToInt, RefusesNonBitVector)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Term a = s->make_symbol("a", s->make_sort(INT));
  EXPECT_THROW(s->make_term(UBV_To_Int, a), IncorrectUsageException);
  EXPECT_THROW(s->make_term(SBV_To_Int, a), IncorrectUsageException);
}

TEST(Yices2SetLogic, RejectedLogicLeavesSolverUsable)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  EXPECT_THROW(s->set_logic("NOT_A_LOGIC"), IncorrectUsageException);
  // QF_NIA needs Yices built with MCSAT, so this build may accept or
  // reject it; either way the solver has to keep working
  try
  {
    s->set_logic("QF_NIA");
  }
  catch (const IncorrectUsageException &)
  {
  }
  Sort intsort = s->make_sort(INT);
  Term x = s->make_symbol("x", intsort);
  s->assert_formula(s->make_term(Equal, x, s->make_term(1, intsort)));
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST(Yices2Context, OptionsKeepAssertions)
{
  // none of these changes the Yices configuration, so setting one after an
  // assertion keeps it
  const std::vector<std::pair<std::string, std::string>> options = {
    { "produce-models", "true" },
    { "time-limit", "10" },
    { "produce-unsat-assumptions", "true" },
  };
  for (const auto & option : options)
  {
    SmtSolver s = Yices2SolverFactory::create(false);
    Sort intsort = s->make_sort(INT);
    Term y = s->make_symbol("y", intsort);
    s->assert_formula(s->make_term(Equal, y, s->make_term(3, intsort)));
    s->set_opt(option.first, option.second);
    s->assert_formula(s->make_term(Equal, y, s->make_term(4, intsort)));
    EXPECT_TRUE(s->check_sat().is_unsat()) << "after setting " << option.first;
  }
}

TEST(Yices2Context, ConfigurationAfterFirstAssertionThrows)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort intsort = s->make_sort(INT);
  Term y = s->make_symbol("y", intsort);
  s->assert_formula(s->make_term(Equal, y, s->make_term(3, intsort)));
  // Yices applies these only when it creates the context, which the
  // assertion did, so changing them now would drop the assertion
  EXPECT_THROW(s->set_opt("incremental", "true"), IncorrectUsageException);
  EXPECT_THROW(s->set_logic("QF_LIA"), IncorrectUsageException);
  s->assert_formula(s->make_term(Equal, y, s->make_term(4, intsort)));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

// Yices numbers terms in the order it makes them after yices_init(), so a
// first symbol gets the same number again only if Yices was freed and set
// up anew in between
TEST(Yices2InstanceRef, ExitsWhenNothingHoldsIt)
{
  std::size_t first_id;
  {
    SmtSolver s = Yices2SolverFactory::create(false);
    first_id = s->make_symbol("x", s->make_sort(BV, 4))->get_id();
  }
  SmtSolver s = Yices2SolverFactory::create(false);
  EXPECT_EQ(s->make_symbol("x", s->make_sort(BV, 4))->get_id(), first_id);
}

TEST(Yices2InstanceRef, StaysWhileATermIsHeld)
{
  Term held;
  {
    SmtSolver s = Yices2SolverFactory::create(false);
    held = s->make_symbol("x", s->make_sort(BV, 4));
  }
  SmtSolver s = Yices2SolverFactory::create(false);
  EXPECT_NE(s->make_symbol("y", s->make_sort(BV, 4))->get_id(), held->get_id());
  EXPECT_EQ(held->to_string(), "x");
}

TEST(Yices2InstanceRef, StaysWhileAnIteratorIsHeld)
{
  vector<string> expected;
  TermIter it, end;
  {
    SmtSolver s = Yices2SolverFactory::create(false);
    Sort bv = s->make_sort(BV, 4);
    Term x = s->make_symbol("x", bv);
    Term y = s->make_symbol("y", bv);
    Term t = s->make_term(BVAnd, x, y);
    for (TermIter i = t->begin(); i != t->end(); ++i)
    {
      expected.push_back((*i)->to_string());
    }
    it = t->begin();
    end = t->end();
  }
  // no term, sort or solver is left, only the iterators
  vector<string> children;
  for (; it != end; ++it)
  {
    children.push_back((*it)->to_string());
  }
  EXPECT_EQ(children, expected);
}

}  // namespace
