/*********************                                                        */
/*! \file cvc4-printinh.cpp
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
 
  return 0;
}
