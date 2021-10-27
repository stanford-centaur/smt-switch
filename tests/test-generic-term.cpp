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
#include <array>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include "assert.h"

// note: this file depends on the CMake build infrastructure
// specifically defined macros
// it cannot be compiled outside of the build
#include "cvc5_factory.h"
#include "generic_sort.h"
#include "generic_term.h"
#include "gtest/gtest.h"
#include "smt.h"
#include "test-utils.h"

using namespace smt;
using namespace std;

int main() { 
  cout << "Testing an integer constant" << endl;
  Sort int_sort = make_generic_sort(INT);
  GenericTerm one(int_sort, Op(), {}, "1");
  GenericTerm one_prime(int_sort, Op(), {}, "1");
  assert(one.get_id() == one_prime.get_id());
  assert(one.hash() == one_prime.hash());
  assert(!one.is_symbol());
  assert(!one.is_param());
  assert(!one.is_symbolic_const());
  
  cout << "Testing an integer variable" << endl;
  GenericTerm x(int_sort, Op(), {}, "x", true);
  GenericTerm x_prime(int_sort, Op(), {}, "x", true);
  assert(x.get_id() == x_prime.get_id());
  assert(x.hash() == x_prime.hash());
  assert(x.is_symbol());
  assert(!x.is_param());
  assert(x.is_symbolic_const());
}
