/*********************                                                        */
/*! \file yices2_term.h
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Yices2 implementation of AbsTerm
**
**
**/

#pragma once

// before yices.h: it declares the mpq_t entry points, among them
// yices_sum_component, only under #ifdef __GMP_H__
#include <gmp.h>

#include <cstdint>
#include <vector>

#include "term.h"
#include "utils.h"
#include "yices.h"
#include "yices2_sort.h"

namespace smt {

// forward declaration
class Yices2Solver;

/** \class Yices2TermIter
 *  Walks a term's children. Yices keeps sums and products as polynomials
 *  rather than as applications, so some children do not exist as terms until
 *  this iterator builds them; see `operator*`.
 */
class Yices2TermIter : public TermIterBase
{
 public:
  Yices2TermIter(term_t t, uint32_t p, bool f);
  Yices2TermIter(const Yices2TermIter & it);
  ~Yices2TermIter() = default;
  Yices2TermIter & operator=(const Yices2TermIter & it);
  void operator++() override;
  const Term operator*() override;
  TermIterBase * clone() const override;
  bool operator==(const Yices2TermIter & it);
  bool operator!=(const Yices2TermIter & it);

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
  term_t term;
  uint32_t pos;
  /* Whether `term` is about a function rather than an array, which is what
   * Yices2Term's own is_function records. A Yices array is a function, so
   * yices_term_is_function cannot tell a child's kind; only the term it
   * came from can.
   */
  bool is_function;
};

class Yices2Term : public AbsTerm
{
 public:
  // assumes that term is not a function if flag is not passed
  Yices2Term(term_t t) : term(t), is_function(false) {};
  Yices2Term(term_t t, bool is_fun) : term(t), is_function(is_fun) {};
  ~Yices2Term() {};
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
  uint64_t to_int() const override;
  int64_t to_signed_int() const override;
  /* Iterators for traversing the children */
  TermIter begin() override;
  TermIter end() override;
  std::string print_value_as(SortKind sk) override;

 protected:
  term_t term;
  bool is_function;

  friend class Yices2TermIter;

  // a const version of to_string
  // the main to_string can't be const so that LoggingSolver
  // can build its string representation lazily
  std::string const_to_string() const;

  friend class Yices2Solver;
};

}  // namespace smt
