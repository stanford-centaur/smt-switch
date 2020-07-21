/*********************                                                        */
/*! \file btor-opts.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for setting options through boolector.
**
**
**/

#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "gtest/gtest.h"

#include "boolector_factory.h"
#include "smt.h"

using namespace smt;
using namespace std;

TEST(BtorOptTest1, Incremental)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  EXPECT_NO_THROW(s->set_opt("incremental", "true"));
  s->assert_formula(s->make_term(false));
  s->check_sat();
  EXPECT_NO_THROW(s->check_sat());
}

TEST(BtorOptTest2, ProduceModels)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  EXPECT_NO_THROW(s->set_opt("produce-models", "true"));
  Sort boolsort = s->make_sort(BOOL);
  Term b = s->make_symbol("b", boolsort);
  s->assert_formula(b);
  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());
  EXPECT_NO_THROW(s->get_value(b));
}

TEST(BtorOptTest3, NonStandardOpt)
{
  // tests an option that's boolector specific
  SmtSolver s = BoolectorSolverFactory::create(false);
  EXPECT_NO_THROW(s->set_opt("nondestr-subst", "true"));
}

TEST(BtorOptTest4, IncorrectOption)
{
  // tests an option that shouldn't exist
  SmtSolver s = BoolectorSolverFactory::create(false);
  EXPECT_THROW(s->set_opt("totally-made-up-option", "true"),
               NotImplementedException);
}
