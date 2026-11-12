/*!
 * \file test-sorting-network.cpp
 * \brief Tests for SortingNetwork
 * \author Makai Mann
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <cstddef>
#include <memory>
#include <string>
#include <tuple>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/sorting_network.h"
#include "smt-switch/term.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SortingNetworkTests);
class SortingNetworkTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<tuple<SolverConfiguration, size_t>>
{
 protected:
  void SetUp() override
  {
    auto params = GetParam();
    solver = create_solver(get<0>(params));
    NUM_VARS = get<1>(params);
    solver->set_opt("produce-models", "true");
    solver->set_opt("incremental", "true");
    boolsort = solver->make_sort(BOOL);
    for (size_t i = 0; i < NUM_VARS; ++i)
    {
      boolvec.push_back(solver->make_symbol("b" + std::to_string(i), boolsort));
    }
  }
  SmtSolver solver;
  Sort boolsort;
  TermVec boolvec;
  size_t NUM_VARS;
};

TEST_P(SortingNetworkTests, TestSortingNetwork)
{
  SortingNetwork sn(solver);
  TermVec sorted = sn.sorting_network(boolvec);

  // Test each possible return value
  for (size_t num_true = 0; num_true <= NUM_VARS; ++num_true)
  {
    solver->push();
    if (num_true)
    {
      // ensure there are at least num_true set to true
      solver->assert_formula(sorted[num_true - 1]);
    }

    if (num_true < NUM_VARS)
    {
      // ensure there aren't more than num_true set to true
      solver->assert_formula(solver->make_term(Not, sorted[num_true]));
    }

    solver->check_sat();

    size_t counted_true = 0;
    string model = "\n";
    Term val;
    for (const auto & bb : boolvec)
    {
      val = solver->get_value(bb);
      if (val->to_bool())
      {
        counted_true++;
      }
      model += "\t" + bb->to_string() + " := " + val->to_string() + "\n";
    }

    EXPECT_EQ(num_true, counted_true)
        << "Incorrect sorting network for model " + model;

    solver->pop();
  }
}

TEST_P(SortingNetworkTests, OutlivesSolverHandle)
{
  SortingNetwork sn{ SmtSolver(solver) };
  TermVec sorted = sn.sorting_network(boolvec);
  EXPECT_EQ(NUM_VARS, sorted.size());
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverSortingNetworkTests,
    SortingNetworkTests,
    testing::Combine(
        testing::ValuesIn(available_non_generic_solver_configurations()),
        testing::Values(3, 6, 8)));

}  // namespace
