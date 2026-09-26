/*********************                                                        */
/*! \file test-generic-sort.cpp
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

#include "generic_datatype.h"
#include "generic_sort.h"
#include "smt.h"

using namespace smt;
using namespace std;

TEST(GenericSort, SortProperties)
{
  GenericSort s1(INT);
  GenericSort s2(INT);
  EXPECT_EQ(s1.hash(), s2.hash());
  EXPECT_EQ(s1.to_string(), s2.to_string());
  EXPECT_EQ(s2.to_string(), s1.to_string());
  EXPECT_EQ(s1.get_sort_kind(), s2.get_sort_kind());
  EXPECT_EQ(s1.get_sort_kind(), INT);

  Sort int1 = make_generic_sort(INT);
  Sort int2 = make_generic_sort(INT);
  EXPECT_EQ(int1, int2);
  Sort bv4 = make_generic_sort(BV, 4);
  Sort bv5 = make_generic_sort(BV, 5);
  EXPECT_NE(bv4, bv5);
  EXPECT_NE(bv4, int1);
  Sort inttobv4 = make_generic_sort(FUNCTION, int1, bv4);
  Sort inttobv4_second = make_generic_sort(FUNCTION, int2, bv4);
  EXPECT_EQ(inttobv4, inttobv4_second);
  Sort arr = make_generic_sort(ARRAY, int1, bv4);
  EXPECT_NE(arr, inttobv4);
  EXPECT_EQ(arr->get_indexsort(), int1);
  EXPECT_EQ(arr->get_elemsort(), bv4);
  EXPECT_EQ(bv4->get_width(), 4);

  Sort us1 = make_uninterpreted_generic_sort("sort1", 0);
  Sort us2 = make_uninterpreted_generic_sort("sort1", 0);
  EXPECT_EQ(us1, us2);
  Sort us3 = make_uninterpreted_generic_sort("sort3", 0);
  EXPECT_NE(us1, us3);
  EXPECT_EQ(us1->get_uninterpreted_name(), "sort1");
  EXPECT_EQ(us1->get_arity(), 0);

  // Creates a new datatype with one constructor
  DatatypeDecl new_dt_decl = make_shared<GenericDatatypeDecl>("testSort1");
  shared_ptr<GenericDatatype> new_dt =
      shared_ptr<GenericDatatype>(new GenericDatatype(new_dt_decl));
  shared_ptr<GenericDatatypeConstructorDecl> new_dt_cons_decl =
      shared_ptr<GenericDatatypeConstructorDecl>(
          new GenericDatatypeConstructorDecl("Cons"));
  new_dt->add_constructor(new_dt_cons_decl);
  shared_ptr<GenericDatatypeSort> dt_sort =
      make_shared<GenericDatatypeSort>(new_dt);

  // Creates a different datatype with one constructor
  DatatypeDecl new2_dt_decl = make_shared<GenericDatatypeDecl>("testSort2");
  shared_ptr<GenericDatatype> new2_dt =
      shared_ptr<GenericDatatype>(new GenericDatatype(new2_dt_decl));
  shared_ptr<GenericDatatypeConstructorDecl> new2_dt_cons_decl =
      shared_ptr<GenericDatatypeConstructorDecl>(
          new GenericDatatypeConstructorDecl("test2"));
  new2_dt->add_constructor(new2_dt_cons_decl);
  shared_ptr<GenericDatatypeSort> dt_sort2 =
      make_shared<GenericDatatypeSort>(new2_dt);
  // Asserts that the sorts are distinct from one another and that the
  // copy operator works with said sorts
  EXPECT_NE(dt_sort, dt_sort2);
  auto copy = dt_sort;
  EXPECT_EQ(dt_sort, copy);
  // Compares string names of the sorts
  EXPECT_NE(dt_sort->to_string(), dt_sort2->to_string());
  // Checks for valid sortKinds
  EXPECT_EQ(dt_sort->get_sort_kind(), dt_sort2->get_sort_kind());
  EXPECT_EQ(dt_sort->get_sort_kind(), DATATYPE);
  EXPECT_EQ(dt_sort2->get_sort_kind(), DATATYPE);
}
