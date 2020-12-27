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
  assert(s1 == s2);
  return 0;
}
