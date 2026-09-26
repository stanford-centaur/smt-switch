/*********************                                                        */
/*! \file msat-traversal.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
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

#include <memory>
#include <vector>

#include "msat_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/msat_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;

TEST(MsatTraversal, ChildrenAndGrandchildren)
{
  SmtSolver s = MsatSolverFactory::create(false);
  s->set_logic("QF_ABV");
  s->set_opt("produce-models", "true");
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term y = s->make_symbol("y", bvsort8);
  Term z = s->make_symbol("z", bvsort8);

  Term a = s->make_term(BVAdd, x, y);
  Term constraint = s->make_term(Equal, z, a);
  s->assert_formula(constraint);

  EXPECT_EQ(constraint->get_op(), Equal);

  // z has no children and x + y has two, so this visits x and y once each
  TermVec children;
  TermVec grandchildren;
  for (auto c : constraint)
  {
    children.push_back(c);
    for (auto t : c)
    {
      grandchildren.push_back(t);
      c->hash();
    }
  }

  EXPECT_EQ(UnorderedTermSet(children.begin(), children.end()),
            UnorderedTermSet({ z, a }));
  EXPECT_EQ(children.size(), 2);
  EXPECT_EQ(UnorderedTermSet(grandchildren.begin(), grandchildren.end()),
            UnorderedTermSet({ x, y }));
  EXPECT_EQ(grandchildren.size(), 2);

  // Identity traversal: rebuild every term from its op and its rebuilt
  // children, which must give back the same term
  UnorderedTermMap cache;
  UnorderedTermSet visited;
  TermVec to_visit{ constraint };
  Term t;
  while (to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();

    if (cache.find(t) != cache.end())
    {
      continue;
    }

    if (visited.find(t) == visited.end())
    {
      // first visit: come back to t after its children
      visited.insert(t);
      to_visit.push_back(t);
      for (auto c : t)
      {
        to_visit.push_back(c);
      }
    }
    else
    {
      TermVec cached_children;
      for (auto c : t)
      {
        cached_children.push_back(cache.at(c));
      }

      if (cached_children.size())
      {
        // rebuild
        cache[t] = s->make_term(t->get_op(), cached_children);
      }
      else
      {
        cache[t] = t;
      }
    }
  }
  EXPECT_EQ(cache.at(constraint), constraint);
}
