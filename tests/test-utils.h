/*********************                                                        */
/*! \file test-utils.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Convenience functions for testing.
**
**
**/

#pragma once

#include <cstdio>
#include <memory>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "smt.h"

// macros for getting string value of another macro
// i.e. STRFY(FOO) := "FOO"
#define STRHELPER(A) #A
#define STRFY(A) STRHELPER(A)

namespace smt_tests {

smt::UnorderedTermSet get_free_symbols(smt::Term & t);
std::string exec(const char * cmd);
void dump_and_run(smt::SolverEnum solver,
                  std::stringbuf & strbuf,
                  std::vector<std::unordered_set<std::string>> expected_results,
                  std::string extra_opts = "");

}  // namespace smt_tests

namespace std {
template <>
struct default_delete<FILE>
{
 public:
  void operator()(FILE * f) const { pclose(f); }
};
}  // namespace std
