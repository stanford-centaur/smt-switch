/*!
 * \file msat-config.cpp
 * \brief Tests the configuration MathSAT's environment is made from.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * msat_set_option checks an option's syntax but not its range, so an
 * out-of-range value is refused only when the environment is made from the
 * configuration, at the first term, sort or query. A query that needs no
 * environment must not make one, or it would fix the configuration.
 * A logic picks a whole configuration, so once there is one, only its own
 * logic is accepted again; with none set, the plain configuration counts as
 * ALL.
 */

#include <gtest/gtest.h>

#include <fstream>
#include <memory>
#include <string>

#include "smt-switch/exceptions.h"
#include "smt-switch/msat_solver.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

using namespace smt;

namespace {

TEST(MsatConfig, AllAcceptedAfterTerm)
{
  SmtSolver s = std::make_shared<MsatSolver>();
  Sort intsort = s->make_sort(INT);
  EXPECT_NO_THROW(s->set_logic("ALL"));
  EXPECT_THROW(s->set_logic("QF_BV"), IncorrectUsageException);
  // the plain configuration has every theory, as ALL asks
  Term x = s->make_symbol("x", intsort);
  Term zero = s->make_term(0, intsort);
  s->assert_formula(s->make_term(Gt, x, zero));
  s->assert_formula(s->make_term(Lt, x, zero));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST(MsatConfig, SameLogicAccepted)
{
  SmtSolver s = std::make_shared<MsatSolver>();
  s->set_logic("QF_BV");
  EXPECT_NO_THROW(s->set_logic("QF_BV"));
  s->make_sort(BV, 4);
  EXPECT_NO_THROW(s->set_logic("QF_BV"));
  EXPECT_THROW(s->set_logic("ALL"), IncorrectUsageException);
}

TEST(MsatConfig, DumpNamesTheLogic)
{
  SmtSolver s = std::make_shared<MsatSolver>();
  s->assert_formula(s->make_symbol("b", s->make_sort(BOOL)));
  std::string filename = testing::TempDir() + "msat-config-logic.smt2";
  s->dump_smt2(filename);
  std::ifstream in(filename);
  std::string first_line;
  std::getline(in, first_line);
  EXPECT_EQ(first_line, "(set-logic ALL)");
}

TEST(MsatConfig, UnknownOptionRefusedBeforeConfig)
{
  SmtSolver s = std::make_shared<MsatSolver>();
  EXPECT_THROW(s->set_opt("no-such-option", "true"), NotImplementedException);
}

TEST(MsatConfig, BadOptionValueRefused)
{
  SmtSolver s = std::make_shared<MsatSolver>();
  EXPECT_THROW(s->set_opt("theory.bv.bit_blast_mode", "abc"),
               IncorrectUsageException);
}

TEST(MsatConfig, RefusedConfigThrows)
{
  SmtSolver s = std::make_shared<MsatSolver>();
  s->set_opt("theory.bv.bit_blast_mode", "99");
  EXPECT_THROW(s->make_sort(BV, 4), IncorrectUsageException);
  // no environment is kept, so the next call is refused too
  EXPECT_THROW(s->make_sort(BV, 4), IncorrectUsageException);
}

TEST(MsatConfig, OptionAcceptedAfterContextLevel)
{
  SmtSolver s = std::make_shared<MsatSolver>();
  s->get_context_level();
  EXPECT_NO_THROW(s->set_opt("produce-models", "true"));
}

TEST(MsatConfig, OptionAcceptedAfterDump)
{
  SmtSolver s = std::make_shared<MsatSolver>();
  s->dump_smt2(testing::TempDir() + "msat-config.smt2");
  EXPECT_NO_THROW(s->set_opt("produce-models", "true"));
}

TEST(MsatConfig, OptionAcceptedAfterResetAssertions)
{
  SmtSolver s = std::make_shared<MsatSolver>();
  s->reset_assertions();
  EXPECT_NO_THROW(s->set_opt("produce-models", "true"));
}

TEST(MsatConfig, UnsatAssumptionsRefusedBeforeCheck)
{
  SmtSolver s = std::make_shared<MsatSolver>();
  UnorderedTermSet out;
  EXPECT_THROW(s->get_unsat_assumptions(out), IncorrectUsageException);
}

}  // namespace
