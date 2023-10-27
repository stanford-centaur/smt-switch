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

#include "api/cpp/cvc5.h"
#include "term.h"
#include "utils.h"

namespace smt {
// forward declaration
class Cvc5Solver;

class Cvc5TermIter : public TermIterBase
{
 public:
  Cvc5TermIter(::cvc5::Term term, uint32_t p = 0) : term(term), pos(p){};
  Cvc5TermIter(const Cvc5TermIter & it)
  {
    term = it.term;
    pos = it.pos;
  };
  ~Cvc5TermIter(){};
  Cvc5TermIter & operator=(const Cvc5TermIter & it);
  void operator++() override;
  const Term operator*() override;
  TermIterBase * clone() const override;
  bool operator==(const Cvc5TermIter & it);
  bool operator!=(const Cvc5TermIter & it);

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
  ::cvc5::Term term;
  uint32_t pos;
};

class Cvc5Term : public AbsTerm
{
 public:
  Cvc5Term(cvc5::Term t) : term(t){};
  ~Cvc5Term(){};
  std::size_t hash() const override;
  std::size_t get_id() const override;
  bool compare(const Term & absterm) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  bool is_symbol() const override;
  bool is_param() const override;
  bool is_symbolic_const() const override;
  bool is_value() const override;
  virtual std::string to_string() override;
  virtual std::wstring getStringValue() override;
  uint64_t to_int() const override;
  /** Iterators for traversing the children
   */
  TermIter begin() override;
  TermIter end() override;
  std::string print_value_as(SortKind sk) override;

  // getters for solver-specific objects
  // for interacting with third-party cvc5-specific software
  ::cvc5::Term get_cvc5_term() const { return term; };

 protected:
  cvc5::Term term;

  friend class Cvc5Solver;
  friend class cvc5InterpolatingSolver;
};

}  // namespace smt
