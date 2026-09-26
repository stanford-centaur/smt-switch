/*********************                                                        */
/*! \file btor-array-empty-assignment.cpp
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

#include "boolector_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/boolector_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

TEST(BtorArrayEmptyAssignment, NoStores)
{
  // This simple test checks that memory is freed correctly
  // even if the array model has no stores

  SmtSolver s = BoolectorSolverFactory::create(false);
  s->set_opt("produce-models", "true");
  Sort bvsort32 = s->make_sort(BV, 32);
  Sort array32_32 = s->make_sort(ARRAY, bvsort32, bvsort32);
  Term arr = s->make_symbol("arr", array32_32);

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  Term out_const_base;
  UnorderedTermMap arr_ass = s->get_array_values(arr, out_const_base);
  EXPECT_EQ(arr_ass.size(), 0);
}
