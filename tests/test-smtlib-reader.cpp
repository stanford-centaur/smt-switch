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

#include <gtest/gtest.h>

#include <cstddef>
#include <memory>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "exceptions.h"
#include "result.h"
#include "smt_defs.h"
#include "smtlib_reader.h"
#include "smtlib_reader_test_inputs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"
#include "utils.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SmtLibReaderTester);
class SmtLibReaderTester : public SmtLibReader
{
 public:
  explicit SmtLibReaderTester(SmtSolver & solver, bool strict = false)
      : SmtLibReader(solver, strict)
  {
  }

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
    // the test files follow SMT-LIB, so a strict reader reads them
    reader = new SmtLibReaderTester(s, true);
  }

  void TearDown() override { delete reader; }

  SmtSolver s;
  SmtLibReaderTester * reader;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IntReaderTests);
class IntReaderTests : public ReaderTests
{
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(RealReaderTests);
class RealReaderTests : public ReaderTests
{
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(StrReaderTests);
class StrReaderTests : public ReaderTests
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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IntRealReaderTests);
class IntRealReaderTests : public ReaderTests
{
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(NonStrictIntRealReaderTests);
class NonStrictIntRealReaderTests : public ReaderTests
{
 protected:
  void SetUp() override
  {
    s = create_solver(get<0>(GetParam()));
    s->set_opt("produce-models", "true");
    // these files use the extensions of the reader outside strict mode
    reader = new SmtLibReaderTester(s, false);
  }
};

TEST_P(IntReaderTests, QF_UFLIA_Smt2Files)
{
  string test = STRFY(SMTLIB_TEST_RESOURCE_DIR);
  auto testpair = get<1>(GetParam());
  test += "/qf_uflia/" + testpair.first;
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

TEST_P(RealReaderTests, QF_LRA_Smt2Files)
{
  string test = STRFY(SMTLIB_TEST_RESOURCE_DIR);
  auto testpair = get<1>(GetParam());
  test += "/qf_lra/" + testpair.first;
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

TEST_P(StrReaderTests, QF_S_Smt2Files)
{
  string test = STRFY(SMTLIB_TEST_RESOURCE_DIR);
  auto testpair = get<1>(GetParam());
  test += "/qf_s/" + testpair.first;
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
  string test = STRFY(SMTLIB_TEST_RESOURCE_DIR);
  auto testpair = get<1>(GetParam());
  test += "/qf_ufbv/" + testpair.first;
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
  if (get<0>(GetParam()).solver_enum == YICES2)
  {
    GTEST_SKIP() << "Yices2 cannot read an array constrained to equal a "
                    "constant array, which test-array.smt2 does";
  }

  string test = STRFY(SMTLIB_TEST_RESOURCE_DIR);
  auto testpair = get<1>(GetParam());
  test += "/qf_alia/" + testpair.first;
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
  string test = STRFY(SMTLIB_TEST_RESOURCE_DIR);
  auto testpair = get<1>(GetParam());
  test += "/qf_uf/" + testpair.first;
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

TEST_P(IntRealReaderTests, QF_LIRA_Smt2Files)
{
  string test = STRFY(SMTLIB_TEST_RESOURCE_DIR);
  auto testpair = get<1>(GetParam());
  test += "/qf_lira/" + testpair.first;
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

TEST_P(NonStrictIntRealReaderTests, QF_LIRA_Smt2Files)
{
  string test = STRFY(SMTLIB_TEST_RESOURCE_DIR);
  auto testpair = get<1>(GetParam());
  test += "/qf_lira/" + testpair.first;
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
    ParameterizedSolverRealReaderTests,
    RealReaderTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { THEORY_REAL })),
                     testing::ValuesIn(qf_lra_tests.begin(),
                                       qf_lra_tests.end())));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverStrReaderTests,
    StrReaderTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { THEORY_INT, THEORY_STR })),
                     testing::ValuesIn(qf_s_tests.begin(), qf_s_tests.end())));

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
                         { THEORY_INT, ARRAY_MODELS, CONSTARR })),
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
    testing::Combine(testing::ValuesIn(
                         filter_solver_configurations({ PARAM_UNINTERP_SORT })),
                     testing::ValuesIn(qf_uf_param_sorts_tests.begin(),
                                       qf_uf_param_sorts_tests.end())));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverIntRealReaderTests,
    IntRealReaderTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { THEORY_INT, THEORY_REAL })),
                     testing::ValuesIn(qf_lira_tests.begin(),
                                       qf_lira_tests.end())));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverNonStrictIntRealReaderTests,
    NonStrictIntRealReaderTests,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { THEORY_INT, THEORY_REAL })),
                     testing::ValuesIn(qf_lira_nonstrict_tests.begin(),
                                       qf_lira_nonstrict_tests.end())));

TEST(UnorderedScopedSymbolMap, PopOutermostScope)
{
  UnorderedScopedSymbolMap map;
  EXPECT_THROW(map.pop_scope(), IncorrectUsageException);
  map.push_scope();
  EXPECT_NO_THROW(map.pop_scope());
  EXPECT_THROW(map.pop_scope(), IncorrectUsageException);
  EXPECT_EQ(map.current_scope(), 0u);
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(Scopes);
class Scopes : public ::testing::Test,
               public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("incremental", "true");
    reader = std::make_unique<SmtLibReader>(s);
    bvsort = s->make_sort(BV, 4);
  }

  SmtSolver s;
  std::unique_ptr<SmtLibReader> reader;
  Sort bvsort;
};

TEST_P(Scopes, PopWithoutPush)
{
  EXPECT_THROW(reader->pop(), IncorrectUsageException);
  EXPECT_THROW(reader->pop_scope(), IncorrectUsageException);
  reader->push();
  EXPECT_NO_THROW(reader->pop());
  EXPECT_THROW(reader->pop(), IncorrectUsageException);
}

TEST_P(Scopes, BindOutsideScope)
{
  Term t = s->make_symbol("t", bvsort);
  EXPECT_THROW(reader->register_arg("x", bvsort), IncorrectUsageException);
  EXPECT_THROW(reader->create_param("y", bvsort), IncorrectUsageException);
  EXPECT_THROW(reader->let_binding("z", t), IncorrectUsageException);
  reader->push_scope();
  EXPECT_NO_THROW(reader->register_arg("x", bvsort));
  EXPECT_NO_THROW(reader->let_binding("z", t));
  EXPECT_NO_THROW(reader->pop_scope());
}

INSTANTIATE_TEST_SUITE_P(
    SmtLibReader,
    Scopes,
    testing::ValuesIn(available_non_generic_solver_configurations()),
    ConfigName());

}  // namespace
