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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SmtLibReaderTester);
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IntReaderTests);
class IntReaderTests : public ReaderTests
{
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(BitVecReaderTests);
class BitVecReaderTests : public ReaderTests
{
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ArrayIntReaderTests);
class ArrayIntReaderTests : public ReaderTests
{
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UninterpReaderTests);
class UninterpReaderTests : public ReaderTests
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

TEST_P(BitVecReaderTests, QF_UFBV_Smt2Files)
{
  // SMT_SWITCH_DIR is a macro defined at build time
  // and should point to the top-level Smt-Switch directory
  string test = STRFY(SMT_SWITCH_DIR);
  auto testpair = get<1>(GetParam());
  test += "/tests/smt2/qf_ufbv/" + testpair.first;
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

TEST_P(ArrayIntReaderTests, QF_ALIA_Smt2Files)
{
  // SMT_SWITCH_DIR is a macro defined at build time
  // and should point to the top-level Smt-Switch directory
  string test = STRFY(SMT_SWITCH_DIR);
  auto testpair = get<1>(GetParam());
  test += "/tests/smt2/qf_alia/" + testpair.first;
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

TEST_P(UninterpReaderTests, QF_UF_Smt2Files)
{
  // SMT_SWITCH_DIR is a macro defined at build time
  // and should point to the top-level Smt-Switch directory
  string test = STRFY(SMT_SWITCH_DIR);
  auto testpair = get<1>(GetParam());
  test += "/tests/smt2/qf_uf/" + testpair.first;
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

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverBitVecReaderTests,
    BitVecReaderTests,
    testing::Combine(
        testing::ValuesIn(available_non_generic_solver_configurations()),
        testing::ValuesIn(qf_ufbv_tests.begin(), qf_ufbv_tests.end())));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverArrayIntReaderTests,
    ArrayIntReaderTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { THEORY_INT, ARRAY_MODELS })),
                     testing::ValuesIn(qf_alia_tests.begin(),
                                       qf_alia_tests.end())));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverUninterpReaderTests,
    UninterpReaderTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { UNINTERP_SORT })),
                     testing::ValuesIn(qf_uf_tests.begin(),
                                       qf_uf_tests.end())));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverParamUninterpReaderTests,
    UninterpReaderTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { PARAM_UNINTERP_SORT })),
                     testing::ValuesIn(qf_uf_param_sorts_tests.begin(),
                                       qf_uf_param_sorts_tests.end())));

}  // namespace smt_tests
