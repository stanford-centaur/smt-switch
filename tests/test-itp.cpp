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

#include <gtest/gtest.h>

#include <ostream>
#include <string>
#include <vector>

#include "available_solvers.h"
#include "smt.h"
#include "utils.h"

using namespace smt;
using namespace std;

namespace smt_tests {

// an interpolator, and the theory it interpolates in: THEORY_INT or
// THEORY_BV
struct ItpParam
{
  SolverConfiguration config;
  SolverAttribute theory;
};

ostream & operator<<(ostream & o, const ItpParam & p)
{
  return o << p.config << " over " << p.theory;
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ItpTests);
class ItpTests : public ::testing::Test,
                 public ::testing::WithParamInterface<ItpParam>
{
 protected:
  void SetUp() override
  {
    itp = create_interpolating_solver(GetParam().config);

    // the queries order the symbols, so unsigned bit-vector comparisons
    // keep them unsatisfiable
    if (GetParam().theory == THEORY_INT)
    {
      sort = itp->make_sort(INT);
      lt = Lt;
      gt = Gt;
    }
    else
    {
      sort = itp->make_sort(BV, 8);
      lt = BVUlt;
      gt = BVUgt;
    }
    x = itp->make_symbol("x", sort);
    y = itp->make_symbol("y", sort);
    z = itp->make_symbol("z", sort);
    w = itp->make_symbol("w", sort);
  }
  SmtSolver itp;
  Sort sort;
  PrimOp lt, gt;
  Term x, y, z, w;
};

TEST_P(ItpTests, Interpolant)
{
  Term A = itp->make_term(lt, x, y);
  A = itp->make_term(And, A, itp->make_term(lt, y, w));

  Term B = itp->make_term(gt, z, w);
  B = itp->make_term(And, B, itp->make_term(lt, z, x));

  Term I;
  Result r = itp->get_interpolant(A, B, I);
  ASSERT_TRUE(r.is_unsat());

  UnorderedTermSet free_symbols;
  get_free_symbolic_consts(I, free_symbols);

  EXPECT_EQ(free_symbols.count(y), 0);
  EXPECT_EQ(free_symbols.count(z), 0);
}

TEST_P(ItpTests, SequenceInterpolants)
{
  // NOTE: there's a default implementation of
  //       get_sequence_interpolants that should work for
  //       any interpolating solver
  //       but it should be much more performant if
  //       specialized with a dedicated function from the
  //       underlying solver
  //       e.g. using interpolation groups in mathsat

  // A1 : x < y /\ y < w
  Term A1 = itp->make_term(lt, x, y);
  A1 = itp->make_term(And, A1, itp->make_term(lt, y, w));

  // A2 : z > w /\ z < x
  Term A2 = itp->make_term(gt, z, w);
  A2 = itp->make_term(And, A2, itp->make_term(lt, z, x));

  // A3 : y > z /\ y < w
  Term A3 = itp->make_term(gt, y, z);
  A3 = itp->make_term(And, A3, itp->make_term(lt, y, w));

  TermVec formulae({ A1, A2, A3 });
  TermVec interpolants;

  Result r = itp->get_sequence_interpolants(formulae, interpolants);
  ASSERT_TRUE(r.is_unsat());
  EXPECT_EQ(interpolants.size(), formulae.size() - 1);
}

TEST_P(ItpTests, ReportsItsSolverEnum)
{
  EXPECT_EQ(itp->get_solver_enum(), GetParam().config.solver_enum);
}

// each interpolator runs the tests in every theory it supports
vector<ItpParam> itp_params()
{
  vector<ItpParam> params;
  for (SolverAttribute theory : { THEORY_INT, THEORY_BV })
  {
    for (SolverConfiguration sc :
         filter_interpolator_configurations({ theory }))
    {
      params.push_back({ sc, theory });
    }
  }
  return params;
}

// names a case after its solver and theory, e.g. CVC5_INT or BZLA_BV
string itp_param_name(const testing::TestParamInfo<ItpParam> & info)
{
  string solver = to_string(info.param.config.solver_enum);
  solver = solver.substr(0, solver.find("_INTERPOLATOR"));
  string theory = to_string(info.param.theory);
  theory = theory.substr(theory.find("THEORY_") + 7);
  string name = solver + "_" + theory;
  if (info.param.config.is_logging_solver)
  {
    name += "_LOGGING";
  }
  return name;
}

INSTANTIATE_TEST_SUITE_P(,
                         ItpTests,
                         testing::ValuesIn(itp_params()),
                         itp_param_name);
}  // namespace smt_tests
