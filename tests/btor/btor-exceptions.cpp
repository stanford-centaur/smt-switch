/*!
 * \file btor-exceptions.cpp
 * \brief Tests that Boolector refuses theories and logics it lacks
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <string>

#include "smt-switch/boolector_factory.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"

using namespace smt;
using namespace std;

TEST(BtorExceptions, UnsupportedTheories)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("produce-models", "true");

  EXPECT_THROW(s->set_logic("QF_NIA"), NotImplementedException);

  EXPECT_THROW(s->make_sort(INT), NotImplementedException);

  Sort bvsort4 = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bvsort4);
  Term y = s->make_symbol("y", bvsort4);

  EXPECT_THROW(s->make_term(Ge, x, y), NotImplementedException);
  EXPECT_THROW(s->make_term(Op(Int_To_BV, 4), x), NotImplementedException);
  EXPECT_THROW(s->make_term(Op(Not, 3), x), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Op(Extract, 3, 0), x, y), IncorrectUsageException);
}

TEST(BtorExceptions, OnlyBitVectorLogics)
{
  for (const string logic :
       { "ALL", "QF_BV", "QF_ABV", "QF_UFBV", "QF_AUFBV", "BV" })
  {
    SmtSolver s = BoolectorSolverFactory::create(false);
    EXPECT_NO_THROW(s->set_logic(logic)) << logic;
  }
  for (const string logic : { "ABV", "UFBV", "AUFBV", "QF_UF", "QF_A" })
  {
    SmtSolver s = BoolectorSolverFactory::create(false);
    EXPECT_THROW(s->set_logic(logic), NotImplementedException) << logic;
  }
  // theories out of SMT-LIB's order
  for (const string logic : { "QF_UFABV", "QF_BVA" })
  {
    SmtSolver s = BoolectorSolverFactory::create(false);
    EXPECT_THROW(s->set_logic(logic), IncorrectUsageException) << logic;
  }
}
