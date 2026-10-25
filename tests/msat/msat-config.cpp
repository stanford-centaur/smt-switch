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
 * configuration, at the first term, sort or query.
 */

#include <gtest/gtest.h>

#include <memory>

#include "mathsat.h"
#include "msat_solver.h"
#include "smt.h"

using namespace smt;

namespace smt_tests {

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

}  // namespace smt_tests
