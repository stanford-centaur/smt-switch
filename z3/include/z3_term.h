/*********************                                                        */
/*! \file z3_term.h
** \verbatim
** Top contributors (to current version):
**   Lindsey Stuntz
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Z3 implementation of AbsTerm
**
**
**/

#pragma once

#include <vector>

//#include "gmp.h"
#include "term.h"
#include "utils.h"
#include "z3++.h"

#include "z3_sort.h"

namespace smt {

// forward declaration
class Z3Solver;

class Z3TermIter : public TermIterBase
{
 public:
//   Z3TermIter(term_t t, uint32_t p) : term(t), pos(p){};
  Z3TermIter(const Z3TermIter & it);
  ~Z3TermIter(){};
  Z3TermIter & operator=(const Z3TermIter & it);
  void operator++() override;
  const Term operator*() override;
  TermIterBase * clone() const override;
  bool operator==(const Z3TermIter & it);
  bool operator!=(const Z3TermIter & it);

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
//   term_t term;
  uint32_t pos;
};

class Z3Term : public AbsTerm
{
 public:
  // assumes that term is not a function if flag is not passed
//   Z3Term(term_t t) : term(t), is_function(false){};
//   Z3Term(term_t t, bool is_fun) : term(t), is_function(is_fun){};
  ~Z3Term(){};
  std::size_t hash() const override;
  bool compare(const Term & absterm) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  bool is_symbol() const override;
  bool is_param() const override;
  bool is_symbolic_const() const override;
  bool is_value() const override;
  virtual std::string to_string() override;
  uint64_t to_int() const override;
  /* Iterators for traversing the children */
  TermIter begin() override;
  TermIter end() override;
  std::string print_value_as(SortKind sk) override;

 protected:
//   term_t term;
  bool is_function;

  // a const version of to_string
  // the main to_string can't be const so that LoggingSolver
  // can build its string representation lazily
  std::string const_to_string() const;

  friend class Z3Solver;
  friend class Z3TermIter;
};

}  // namespace smt
