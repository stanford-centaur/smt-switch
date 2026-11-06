/*********************                                                        */
/*! \file cvc5_term.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief cvc5 implementation of AbsTerm
**
**
**/

#pragma once

#include <cvc5/cvc5.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "ops.h"
#include "smt_defs.h"
#include "sort.h"
#include "term.h"

namespace smt {
class Cvc5TermIter : public TermIterBase
{
 public:
  explicit Cvc5TermIter(::cvc5::Term t, std::size_t pos = 0);
  TermIterBase * clone() const override;

 protected:
  Term child() const override;
  bool same_term(const TermIterBase & other) const override;

 private:
  ::cvc5::Term term;
};

class Cvc5Term : public AbsTerm
{
 public:
  explicit Cvc5Term(cvc5::Term t);
  std::size_t hash() const override;
  std::size_t get_id() const override;
  bool compare(const Term & absterm) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  bool is_symbol() const override;
  bool is_param() const override;
  bool is_symbolic_const() const override;
  bool is_value() const override;
  virtual std::string to_string() const override;
  virtual std::wstring getStringValue() const override;
  std::string get_symbol_name() const override;
  uint64_t to_int() const override;
  int64_t to_signed_int() const override;
  /** Iterators for traversing the children
   */
  TermIter begin() const override;
  TermIter end() const override;
  std::string print_value_as(SortKind sk) const override;

  // Getters for solver-specific objects
  // for interacting with third-party cvc5-specific software
  ::cvc5::Term get_cvc5_term() const;

 protected:
  cvc5::Term term;

  friend class Cvc5Solver;
  friend class cvc5InterpolatingSolver;
};

/** The cvc5 kind of the applications of po
 *  @throws IncorrectUsageException for NUM_OPS_AND_NULL or an out-of-range
 *          value
 */
cvc5::Kind to_cvc5_kind(PrimOp po);

/** The PrimOp of the applications of kind
 *  @throws NotImplementedException for a kind that no PrimOp stands for
 */
PrimOp to_primop(cvc5::Kind kind);

}  // namespace smt
