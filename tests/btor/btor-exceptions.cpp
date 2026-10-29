/*********************                                                        */
/*! \file btor-exceptions.cpp
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

#include <string>

#include "boolector_factory.h"
#include "exceptions.h"
#include "ops.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"

using namespace smt;
using namespace std;

TEST(BtorExceptions, UnsupportedTheories)
{
  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("produce-models", "true");

  EXPECT_THROW(s->set_logic("QF_NIA"), IncorrectUsageException);

  EXPECT_THROW(s->make_sort(INT), NotImplementedException);

  Sort bvsort4 = s->make_sort(BV, 4);
  Term x = s->make_symbol("x", bvsort4);
  Term y = s->make_symbol("y", bvsort4);

  EXPECT_THROW(s->make_term(Ge, x, y), IncorrectUsageException);
}
