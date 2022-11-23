/*********************                                                        */
/*! \file test-itp.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for interpolant generation.
**
**
**/

#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"
#include "test-utils.h"

using namespace smt;
using namespace std;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ItpTests);
class ItpTests : public ::testing::Test,
                 public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    itp = create_interpolating_solver(GetParam());

    intsort = itp->make_sort(INT);
    x = itp->make_symbol("x", intsort);
    y = itp->make_symbol("y", intsort);
    z = itp->make_symbol("z", intsort);
    w = itp->make_symbol("w", intsort);
  }
  SmtSolver itp;
  Sort intsort;
  Term x, y, z, w;
};

TEST_P(ItpTests, Test_ITP)
{
  Term A = itp->make_term(Lt, x, y);
  A = itp->make_term(And, A, itp->make_term(Lt, y, w));

  Term B = itp->make_term(Gt, z, w);
  B = itp->make_term(And, B, itp->make_term(Lt, z, x));

  Term I;
  Result r = itp->get_interpolant(A, B, I);
  ASSERT_TRUE(r.is_unsat());

  UnorderedTermSet free_symbols = get_free_symbols(I);

  ASSERT_TRUE(free_symbols.find(y) == free_symbols.end());
  ASSERT_TRUE(free_symbols.find(z) == free_symbols.end());
  std::cout << "the interpolant is: " << I << endl;
}

TEST_P(ItpTests, TEST_SEQITP)
{
  // NOTE: there's a default implementation of
  //       get_sequence_interpolants that should work for
  //       any interpolating solver
  //       but it should be much more performant if
  //       specialized with a dedicated function from the
  //       underlying solver
  //       e.g. using interpolation groups in mathsat

  // A1 : x < y /\ y < w
  Term A1 = itp->make_term(Lt, x, y);
  A1 = itp->make_term(And, A1, itp->make_term(Lt, y, w));

  // A2 : z > w /\ z < x
  Term A2 = itp->make_term(Gt, z, w);
  A2 = itp->make_term(And, A2, itp->make_term(Lt, z, x));

  // A3 : y > z /\ y < w
  Term A3 = itp->make_term(Gt, y, z);
  A3 = itp->make_term(And, A3, itp->make_term(Lt, y, w));

  TermVec formulae({ A1, A2, A3 });
  TermVec interpolants;

  Result r = itp->get_sequence_interpolants(formulae, interpolants);
  ASSERT_TRUE(r.is_unsat());

  for (auto I : interpolants)
  {
    std::cout << "got seq-itp: " << I << std::endl;
  }
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedItpTests,
    ItpTests,
    testing::ValuesIn(available_interpolator_configurations()));
}  // namespace smt_tests
