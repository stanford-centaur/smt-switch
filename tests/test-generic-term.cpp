/*********************                                                        */
/*! \file test-generic-term.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
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
#include <string>

// note: this file depends on the CMake build infrastructure
// specifically defined macros
// it cannot be compiled outside of the build
#include "generic_sort.h"
#include "generic_term.h"
#include "smt.h"

using namespace smt;

TEST(GenericTerm, IdsAndProperties)
{
  Sort int_sort = std::make_shared<GenericSort>(INT);
  GenericTerm one(int_sort, Op(), {}, "1");
  GenericTerm one_prime(int_sort, Op(), {}, "1");
  EXPECT_EQ(one.get_id(), one_prime.get_id());
  EXPECT_EQ(one.hash(), one_prime.hash());
  EXPECT_FALSE(one.is_symbol());
  EXPECT_FALSE(one.is_param());
  EXPECT_FALSE(one.is_symbolic_const());

  GenericTerm x(int_sort, Op(), {}, "x", true);
  GenericTerm x_prime(int_sort, Op(), {}, "x", true);
  EXPECT_EQ(x.get_id(), x_prime.get_id());
  EXPECT_EQ(x.hash(), x_prime.hash());
  EXPECT_TRUE(x.is_symbol());
  EXPECT_FALSE(x.is_param());
  EXPECT_TRUE(x.is_symbolic_const());
}
