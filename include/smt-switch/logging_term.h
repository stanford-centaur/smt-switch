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
#ifndef SMT_SWITCH_LOGGING_TERM_H
#define SMT_SWITCH_LOGGING_TERM_H

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {

class LoggingTerm : public AbsTerm
{
 public:
  LoggingTerm(Term t, Sort s, Op o, TermVec c, std::size_t id);
  // this one is for making symbols
  // if passed with true, sets is_sym true
  // otherwise sets is_param true
  // only symbols and parameters have names
  LoggingTerm(Term t,
              Sort s,
              Op o,
              TermVec c,
              std::string r,
              bool symbol,
              std::size_t id);
  // this one is for a named leaf that is neither a symbol nor a parameter,
  // such as a datatype's constructor, selector or tester
  LoggingTerm(Term t, Sort s, std::string r, std::size_t id);

  // implemented

  std::size_t get_id() const override;
  /** Returns true iff the underlying term AND sort are equivalent
   *  @param t the term to compare with (assumed to be LoggingTerm)
   *  @return true iff the underlying term and sort match t
   */
  bool compare(const Term & t) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  std::string to_string() const override;
  std::wstring getStringValue() const override;
  bool is_symbol() const override;
  bool is_param() const override;
  bool is_symbolic_const() const override;

  // dispatched to underlying term
  std::size_t hash() const override;
  bool is_value() const override;
  std::string get_constructor_name() const override;
  std::string get_param_name() const override;
  std::string get_selector_name() const override;
  std::string get_symbol_name() const override;
  std::uint64_t to_int() const override;
  std::int64_t to_signed_int() const override;
  bool to_bool() const override;
  std::string print_value_as(SortKind sk) const override;

 protected:
  std::size_t get_num_children() const override;
  Term get_child(std::size_t i) const override;

  Term wrapped_term;  ///< the term of the underlying solver
  Sort sort;          ///< a LoggingSort
  Op op = {};
  // null for a leaf
  std::shared_ptr<const TermVec> children = nullptr;
  mutable std::string repr = "";
  bool is_sym = false;
  bool is_par = false;
  std::size_t id_;  ///< unique id for this term

  // So LoggingSolver can access protected members:
  friend class LoggingSolver;
};

}  // namespace smt

#endif  // SMT_SWITCH_LOGGING_TERM_H
