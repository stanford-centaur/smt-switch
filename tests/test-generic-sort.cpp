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
#include <fstream>
#include <cstdio>
#include <stdexcept>
#include <string>
#include <array>
#include <iostream>
#include <memory>
#include <vector>
#include <sstream>
#include "assert.h"

// note: this file depends on the CMake build infrastructure
// specifically defined macros
// it cannot be compiled outside of the build
#include "test-utils.h"
#include "gtest/gtest.h"
#include "cvc4_factory.h"
#include "generic_sort.h"
#include "smt.h"

using namespace smt;
using namespace std;

int main()
{
  GenericSort s1(INT);
  GenericSort s2(INT);
  std::cout << "testing basic properties of sorts" << std::endl;
  assert(s1.hash() == s2.hash());
  assert(s1.to_string() == s2.to_string());
  assert(s2.to_string() == s1.to_string());
  assert((s1.get_sort_kind()) == (s2.get_sort_kind()));
  assert(s1.get_sort_kind() == INT);

  Sort int1 = make_generic_sort(INT);
  Sort int2 = make_generic_sort(INT);
  assert(int1 == int2);
  Sort bv4 = make_generic_sort(BV, 4);
  Sort bv5 = make_generic_sort(BV, 5);
  assert(bv4 != bv5);
  assert(bv4 != int1);
  Sort inttobv4 = make_generic_sort(FUNCTION, int1, bv4);
  Sort inttobv4_second = make_generic_sort(FUNCTION, int2, bv4);
  assert(inttobv4 == inttobv4_second);
  Sort arr = make_generic_sort(ARRAY, int1, bv4);
  assert(arr != inttobv4);
  assert(arr->get_indexsort() == int1);
  assert(arr->get_elemsort() == bv4);
  assert(bv4->get_width() == 4);

  Sort us1 = make_uninterpreted_generic_sort("sort1", 0);
  Sort us2 = make_uninterpreted_generic_sort("sort1", 0);
  assert(us1 == us2);
  Sort us3 = make_uninterpreted_generic_sort("sort3", 0);
  assert(us1 != us3);
  assert(us1->get_uninterpreted_name() == "sort1");
  assert(us1->get_arity() == 0);
  cout << "pre datatype" << endl;
  DatatypeDecl new_dt_decl = make_shared<GenericDatatypeDecl>("testSort1");
  shared_ptr<GenericDatatype> new_dt =
      shared_ptr<GenericDatatype>(new GenericDatatype(new_dt_decl));
  shared_ptr<GenericDatatypeConstructorDecl> new_dt_cons_decl =
      shared_ptr<GenericDatatypeConstructorDecl>(
          new GenericDatatypeConstructorDecl("Cons"));
  new_dt->add_constructor(new_dt_cons_decl);
  shared_ptr<GenericDatatypeSort> dt_sort =
      make_shared<GenericDatatypeSort>(new_dt);

  DatatypeDecl new2_dt_decl = make_shared<GenericDatatypeDecl>("testSort2");
  shared_ptr<GenericDatatype> new2_dt =
      shared_ptr<GenericDatatype>(new GenericDatatype(new2_dt_decl));
  shared_ptr<GenericDatatypeConstructorDecl> new2_dt_cons_decl =
      shared_ptr<GenericDatatypeConstructorDecl>(
          new GenericDatatypeConstructorDecl("test2"));
  new2_dt->add_constructor(new2_dt_cons_decl);

  shared_ptr<GenericDatatypeSort> dt_sort2 =
      make_shared<GenericDatatypeSort>(new2_dt);
  assert(dt_sort != dt_sort2);
  auto copy = dt_sort;
  assert(dt_sort == copy);
  cout << dt_sort->compute_string() << endl;
  cout << dt_sort2->compute_string() << endl;
  assert(dt_sort->to_string() != dt_sort2->to_string());
  assert((dt_sort->get_sort_kind()) == (dt_sort2->get_sort_kind()));
  assert(dt_sort->get_sort_kind() == DATATYPE);
  assert(dt_sort2->get_sort_kind() == DATATYPE);

  /*
  GenericSort d1(DATATYPE);
  GenericSort d2(DATATYPE);
  std::cout << "testing basic properties of datatype sorts" << std::endl;
  assert(d1.hash() == d2.hash());
  assert(d1.to_string() == d2.to_string());
  cout << d1.to_string() << endl;
  assert(d2.to_string() == d1.to_string());
  assert((d1.get_sort_kind()) == (d2.get_sort_kind()));
  assert(d1.get_sort_kind() == DATATYPE);
  cout << "almost there" << endl;
  Sort dt1 = make_generic_sort(DATATYPE);
  Sort dt2 = make_generic_sort(DATATYPE);
  assert(dt1 == dt2);
  */

  return 0;
}
