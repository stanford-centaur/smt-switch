/*!
 * \file test-generic-term.cpp
 * \brief Tests GenericTerm's ids, properties and constructor checks
 * \author Yoni Zohar
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <memory>
#include <string>

#include "smt-switch/exceptions.h"
#include "smt-switch/generic_sort.h"
#include "smt-switch/generic_term.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"

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

TEST(GenericTerm, NeedsOpOrRepresentation)
{
  Sort int_sort = std::make_shared<GenericSort>(INT);
  EXPECT_THROW(GenericTerm(int_sort, Op(), {}, ""), IncorrectUsageException);
  EXPECT_THROW(GenericTerm(int_sort, Op(), {}, "", true),
               IncorrectUsageException);
}
