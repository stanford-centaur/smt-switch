/*!
 * \file msat-config.cpp
 * \brief Tests the configuration MathSAT's environment is made from.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * MathSAT has no logic option: a logic picks a whole configuration, made
 * with msat_create_default_config, so a configuration the caller passed in
 * is left alone.
 * msat_set_option checks an option's syntax but not its range, so an
 * out-of-range value is refused only when the environment is made from the
 * configuration, at the first term, sort or query. A query that needs no
 * environment must not make one, or it would fix the configuration.
 */

#include <gtest/gtest.h>

#include <memory>
#include <string>

#include "mathsat.h"
#include "msat_solver.h"
#include "smt.h"

using namespace smt;

namespace {

TEST(MsatConfig, CallerConfigRefusesLogic)
{
  SmtSolver s = std::make_shared<MsatSolver>(msat_create_config());
  EXPECT_THROW(s->set_logic("QF_BV"), IncorrectUsageException);
}

TEST(MsatConfig, UnknownOptionRefusedBeforeConfig)
{
  SmtSolver s = std::make_shared<MsatSolver>();
  EXPECT_THROW(s->set_opt("no-such-option", "true"), InternalSolverException);
}

TEST(MsatConfig, RefusedConfigThrows)
{
  SmtSolver s = std::make_shared<MsatSolver>();
  s->set_opt("theory.bv.bit_blast_mode", "99");
  EXPECT_THROW(s->make_sort(BV, 4), InternalSolverException);
  // no environment is kept, so the next call is refused too
  EXPECT_THROW(s->make_sort(BV, 4), InternalSolverException);
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
