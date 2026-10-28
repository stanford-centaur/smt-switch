/*********************                                                        */
/*! \file result.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief The result of a call to check-sat or check-sat-assuming.
**
**
**/

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#pragma once

#include <ostream>
#include <string>

namespace smt {

enum ResultType
{
  SAT = 0,
  UNSAT,
  UNKNOWN,
  /** IMPORTANT: This must stay at the bottom.
      It's only use is for sizing the result2str array
  */
  NUM_RESULTS
};

struct Result
{
  Result() = default;
  explicit Result(ResultType rt, std::string reason = "no explanation");
  bool is_sat() const;
  bool is_unsat() const;
  bool is_unknown() const;
  bool is_null() const;
  std::string get_explanation() const;
  std::string to_string() const;
  ResultType result = NUM_RESULTS;
  std::string explanation = "null";
};

std::ostream & operator<<(std::ostream & output, const Result r);
bool operator==(const Result & r1, const Result & r2);
bool operator!=(const Result & r1, const Result & r2);

}  // namespace smt
