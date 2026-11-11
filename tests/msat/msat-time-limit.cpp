/*!
 * \file msat-time-limit.cpp
 * \brief MathSAT time limits outside what the general time-limit suite checks
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Every other MathSAT option that has an effect is fixed once the environment
 * exists, and the general suite runs no interpolators.
 */
#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "smt-switch/exceptions.h"
#include "smt-switch/interpolator.h"
#include "smt-switch/msat_factory.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

using namespace smt;

namespace {

/** @return the constraints of a pigeonhole problem too hard to finish
 *  inside a short limit, each pigeon in a hole of its own
 */
TermVec pigeonhole(AbsSmtSolver & s)
{
  Sort bvsort = s.make_sort(BV, 6);
  TermVec vars;
  for (size_t i = 0; i < 65; ++i)
  {
    vars.push_back(s.make_symbol("x" + std::to_string(i), bvsort));
  }
  TermVec distincts;
  for (size_t i = 0; i < vars.size(); ++i)
  {
    for (size_t j = i + 1; j < vars.size(); ++j)
    {
      distincts.push_back(s.make_term(Distinct, vars[i], vars[j]));
    }
  }
  return distincts;
}

TEST(MsatTimeLimit, AcceptedOnceTheEnvironmentExists)
{
  SmtSolver s = MsatSolverFactory::create(false);
  TermVec distincts = pigeonhole(*s);
  EXPECT_THROW(s->set_opt("time-limit", "-1"), IncorrectUsageException);
  s->set_opt("time-limit", "0.1");
  for (const Term & d : distincts)
  {
    s->assert_formula(d);
  }
  Result r = s->check_sat();
  EXPECT_TRUE(r.is_unknown());
  EXPECT_EQ(r.get_explanation(), "Time limit reached.");
}

TEST(MsatTimeLimit, StopsAnInterpolationQuery)
{
  SmtInterpolator s = MsatSolverFactory::create_interpolator();
  s->set_opt("time-limit", "0.1");
  TermVec distincts = pigeonhole(*s);
  const size_t half = distincts.size() / 2;
  Term A =
      s->make_term(And, TermVec(distincts.begin(), distincts.begin() + half));
  Term B =
      s->make_term(And, TermVec(distincts.begin() + half, distincts.end()));
  Term I;
  Result r = s->get_interpolant(A, B, I);
  EXPECT_TRUE(r.is_unknown());
  EXPECT_EQ(r.get_explanation(), "Time limit reached.");

  // the interpolator still answers once a query is cut off
  Sort intsort = s->make_sort(INT);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  EXPECT_TRUE(
      s->get_interpolant(s->make_term(Lt, x, y), s->make_term(Lt, y, x), I)
          .is_unsat());
  EXPECT_TRUE(I);
}

}  // namespace
