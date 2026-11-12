/*!
 * \file unit-set-opt.cpp
 * \brief Tests that set_opt refuses what no solver may accept
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * An option the solver does not know is refused with
 * NotImplementedException. The Boolean options smt-switch interprets
 * itself take true or false, as SMT-LIB writes them, and any other value
 * is refused with IncorrectUsageException, even where the solver would
 * read it.
 */
#include <gtest/gtest.h>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"

using namespace smt;
using namespace smt_tests;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SetOpt);
class SetOpt : public ::testing::Test,
               public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override { s = create_solver(GetParam()); }

  SmtSolver s;
};

TEST_P(SetOpt, UnknownOption)
{
  EXPECT_THROW(s->set_opt("no-such-option", "true"), NotImplementedException);
}

TEST_P(SetOpt, BooleanOptionTakesTrueOrFalse)
{
  for (const char * option :
       { "produce-models", "incremental", "produce-unsat-assumptions" })
  {
    for (const char * value : { "1", "0", "maybe" })
    {
      EXPECT_THROW(s->set_opt(option, value), IncorrectUsageException)
          << option << " " << value;
    }
  }
}

INSTANTIATE_TEST_SUITE_P(,
                         SetOpt,
                         testing::ValuesIn(available_solver_configurations()),
                         ConfigName());

}  // namespace
