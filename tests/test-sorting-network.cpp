/*********************                                                        */
/*! \file test-disjointset.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for SortingNetwork.
**
**
**/

#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "available_solvers.h"
#include "smt.h"
#include "sorting_network.h"
#include "utils.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class SortingNetworkTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    solver = create_solver(GetParam());
    solver->set_opt("produce-models", "true");
    boolsort = solver->make_sort(BOOL);
    for (size_t i = 0; i < NUM_VARS; ++i)
    {
      boolvec.push_back(solver->make_symbol("b" + std::to_string(i), boolsort));
    }
  }
  SmtSolver solver;
  Sort boolsort;
  TermVec boolvec;
  size_t NUM_VARS = 8;
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

    Term true_ = solver->make_term(true);
    size_t counted_true = 0;
    string model = "\n";
    Term val;
    for (const auto & bb : boolvec)
    {
      val = solver->get_value(bb);
      if (val == true_)
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

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverSortingNetworkTests,
    SortingNetworkTests,
    testing::ValuesIn(available_non_generic_solver_configurations()));

}  // namespace smt_tests
