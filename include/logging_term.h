/*********************                                                        */
/*! \file logging_term.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class that wraps another Term object and maintains the expected
**        Op and children (for solvers that rewrite terms on the fly).
**
**/

#pragma once

#include <cstddef>
#include <cstdint>
#include <string>

#include "ops.h"
#include "smt_defs.h"
#include "term.h"

namespace smt {

class LoggingTerm : public AbsTerm
{
 public:
  LoggingTerm(Term t, Sort s, Op o, TermVec c, size_t id);
  // this one is for making symbols
  // if passed with true, sets is_sym true
  // otherwise sets is_param true
  // only symbols and parameters have names
  LoggingTerm(
      Term t, Sort s, Op o, TermVec c, std::string r, bool is_sym, size_t id);
  virtual ~LoggingTerm();

  // implemented

  std::size_t get_id() const override;
  /** Returns true iff the underlying term AND sort are equivalent
   *  @param t the term to compare with (assumed to be LoggingTerm)
   *  @return true iff the underlying term and sort match t
   */
  bool compare(const Term & t) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  std::string to_string() override;
  std::wstring getStringValue() const override;
  bool is_symbol() const override;
  bool is_param() const override;
  bool is_symbolic_const() const override;
  TermIter begin() override;
  TermIter end() override;

  // dispatched to underlying term
  std::size_t hash() const override;
  bool is_value() const override;
  uint64_t to_int() const override;
  std::string print_value_as(SortKind sk) override;

 protected:
  Term wrapped_term;  ///< the term of the underlying solver
  Sort sort;          ///< a LoggingSort
  Op op;
  TermVec children;
  std::string repr;
  bool is_sym;
  bool is_par;
  size_t id_;  ///< unique id for this term

  // So LoggingSolver can access protected members:
  friend class LoggingSolver;
};

class LoggingTermIter : public TermIterBase
{
 public:
  LoggingTermIter(TermVec::iterator i);
  LoggingTermIter(const LoggingTermIter & lit);
  ~LoggingTermIter();
  LoggingTermIter & operator=(const LoggingTermIter & lit);
  void operator++() override;
  const Term operator*() override;
  TermIterBase * clone() const override;
  bool operator==(const LoggingTermIter & lit);
  bool operator!=(const LoggingTermIter & lit);

 protected:
  bool equal(const TermIterBase & other) const override;
  TermVec::iterator it;
};

}  // namespace smt
