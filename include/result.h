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

#ifndef SMT_RESULT_H
#define SMT_RESULT_H

namespace smt
{
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
  Result() : result(NUM_RESULTS), explanation("null") {}
  Result(ResultType rt, std::string explanation = "")
      : result(rt), explanation(explanation)
  {
  }
  bool is_sat() { return result == SAT; };
  bool is_unsat() { return result == UNSAT; };
  bool is_unknown() { return result == UNKNOWN; };
  bool is_null() { return result == NUM_RESULTS; };
  std::string to_string() const;
  ResultType result;
  std::string explanation;
  };

  std::ostream & operator<<(std::ostream & output, const Result r);
}

#endif
