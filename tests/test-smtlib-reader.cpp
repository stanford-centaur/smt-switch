/*********************                                                        */
/*! \file test-smtlib-reader.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Test the SmtLibReader (if enabled)
**
**
**/

#define STRHELPER(A) #A
#define STRFY(A) STRHELPER(A)

#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "available_solvers.h"
#include "smt.h"
#include "smtlib_reader.h"
#include "smtlib_reader_test_inputs.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class SmtLibReaderTester : public SmtLibReader
{
 public:
  SmtLibReaderTester(SmtSolver & solver) : SmtLibReader(solver) {}

  Result check_sat() override
  {
    Result r = solver_->check_sat();
    // save the result to compare later
    results_.push_back(r);
    return r;
  }

  Result check_sat_assuming(const TermVec & assumptions) override
  {
    Result r = solver_->check_sat_assuming(assumptions);
    // save the result to compare later
    results_.push_back(r);
    return r;
  }

  const vector<Result> & get_results() const { return results_; };

 protected:
  vector<Result> results_;
};

class ReaderTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<
          tuple<SolverConfiguration, pair<const string, vector<Result>>>>
{
 protected:
  void SetUp() override
  {
    s = create_solver(get<0>(GetParam()));
    s->set_opt("produce-models", "true");
    reader = new SmtLibReaderTester(s);
  }

  void TearDown() override { delete reader; }

  SmtSolver s;
  SmtLibReaderTester * reader;
};

class IntReaderTests : public ReaderTests
{
};

TEST_P(IntReaderTests, QF_UFLIA_Smt2Files)
{
  // SMT_SWITCH_DIR is a macro defined at build time
  // and should point to the top-level Smt-Switch directory
  string test = STRFY(SMT_SWITCH_DIR);
  auto testpair = get<1>(GetParam());
  test += "/tests/smt2/qf_uflia/" + testpair.first;
  reader->parse(test);
  auto results = reader->get_results();
  auto expected_results = testpair.second;
  ASSERT_EQ(results.size(), expected_results.size());

  size_t size = results.size();
  for (size_t i = 0; i < size; i++)
  {
    EXPECT_EQ(results[i], expected_results[i]);
  }
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverIntReaderTests,
    IntReaderTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { THEORY_INT })),
                     testing::ValuesIn(qf_uflia_tests.begin(),
                                       qf_uflia_tests.end())));

}  // namespace smt_tests
