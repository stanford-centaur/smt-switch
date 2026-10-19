/*********************                                                        */
/*! \file test-portfolio-solver.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
**
**
**/

#include <gtest/gtest.h>

#include <unordered_set>
#include <vector>

#include "available_solvers.h"
#include "portfolio_solver.h"
#include "smt.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

/** The available backends that have the attributes and can take part in a
 *  portfolio. The generic solver cannot: a portfolio hands each member its
 *  term through a TermTranslator, which refuses the generic solver.
 */
vector<SolverEnum> backends_with(
    const unordered_set<SolverAttribute> & attributes)
{
  vector<SolverEnum> backends;
  for (SolverEnum se : filter_solver_enums(attributes))
  {
    if (se != GENERIC_SOLVER)
    {
      backends.push_back(se);
    }
  }
  return backends;
}

/** A fresh solver from each backend that has the attributes */
vector<SmtSolver> members_with(
    const unordered_set<SolverAttribute> & attributes)
{
  vector<SmtSolver> members;
  for (SolverEnum se : backends_with(attributes))
  {
    members.push_back(create_solver(SolverConfiguration(se, false)));
  }
  return members;
}

/** Two fresh solvers from each backend that has the attributes, made once in
 *  order and once in reverse, so that several instances of a backend are
 *  alive at once and are not all made back to back
 */
vector<SmtSolver> two_members_each_with(
    const unordered_set<SolverAttribute> & attributes)
{
  vector<SolverEnum> backends = backends_with(attributes);
  vector<SmtSolver> members;
  for (auto it = backends.begin(); it != backends.end(); ++it)
  {
    members.push_back(create_solver(SolverConfiguration(*it, false)));
  }
  for (auto it = backends.rbegin(); it != backends.rend(); ++it)
  {
    members.push_back(create_solver(SolverConfiguration(*it, false)));
  }
  return members;
}

/** A fresh solver from each backend without the attribute */
vector<SmtSolver> members_without(SolverAttribute attribute)
{
  vector<SmtSolver> members;
  for (SolverEnum se : backends_with({}))
  {
    if (!solver_has_attribute(se, attribute))
    {
      members.push_back(create_solver(SolverConfiguration(se, false)));
    }
  }
  return members;
}

/** A solver from the first backend that has the attributes, to make a term
 *  in that no member shares
 */
SmtSolver term_maker(const unordered_set<SolverAttribute> & attributes)
{
  return create_solver(
      SolverConfiguration(backends_with(attributes).front(), false));
}

// x > 0 over the integers, which not every backend supports.
Term make_int_term()
{
  SmtSolver s = term_maker({ THEORY_INT });
  Sort int_sort = s->make_sort(INT);
  Term x = s->make_symbol("x", int_sort);
  return s->make_term(Gt, x, s->make_term(0, int_sort));
}

}  // namespace

TEST(PortfolioSolver, TwoPortfoliosFindSat)
{
  if (backends_with({ THEORY_BV }).empty())
  {
    GTEST_SKIP() << "no backend with bit-vectors";
  }
  SmtSolver s = term_maker({ THEORY_BV });
  s->set_opt("produce-models", "true");
  Sort bvsort = s->make_sort(BV, 10);

  int pg = 50;

  vector<Term> nts;
  for (int i = 0; i < pg; ++i)
  {
    Term x = s->make_symbol("x" + to_string(i), bvsort);
    nts.push_back(x);
  }

  Term ten24 = s->make_term(256, bvsort);
  vector<Term> neqs;
  for (int i = 0; i < pg; ++i)
  {
    for (int j = 0; j < pg; ++j)
    {
      if (i != j)
      {
        Term x = s->make_term(Not, s->make_term(Equal, nts[i], nts[j]));
        neqs.push_back(x);
      }
    }
    Term y = s->make_term(BVSle, nts[i], ten24);
    neqs.push_back(y);
  }

  Term test_term = s->make_term(Equal, neqs[0], neqs[0]);
  for (Term t : neqs)
  {
    test_term = s->make_term(And, t, test_term);
  }

  PortfolioSolver p(two_members_each_with({ THEORY_BV }), test_term);
  EXPECT_TRUE(p.portfolio_solve().is_sat());

  PortfolioSolver p2(two_members_each_with({ THEORY_BV }), test_term);
  EXPECT_TRUE(p2.portfolio_solve().is_sat());
}

TEST(PortfolioSolver, FailingSolverDropsOut)
{
  vector<SmtSolver> members = members_without(THEORY_INT);
  vector<SmtSolver> answering = members_with({ THEORY_INT });
  if (members.empty() || answering.empty())
  {
    GTEST_SKIP() << "needs backends both with and without integers";
  }
  members.insert(members.end(), answering.begin(), answering.end());
  PortfolioSolver p(members, make_int_term());
  EXPECT_TRUE(p.portfolio_solve().is_sat());
}

TEST(PortfolioSolver, ThrowsWhenNoSolverAnswers)
{
  vector<SmtSolver> members = members_without(THEORY_INT);
  if (members.empty() || backends_with({ THEORY_INT }).empty())
  {
    GTEST_SKIP() << "needs backends both with and without integers";
  }
  PortfolioSolver p(members, make_int_term());
  EXPECT_THROW(p.portfolio_solve(), SmtException);
}

TEST(PortfolioSolver, CanBeUsedAgain)
{
  if (backends_with({ THEORY_INT }).empty())
  {
    GTEST_SKIP() << "no backend with integers";
  }
  PortfolioSolver p(members_with({ THEORY_INT }), make_int_term());
  EXPECT_TRUE(p.portfolio_solve().is_sat());
  EXPECT_TRUE(p.portfolio_solve().is_sat());
}
