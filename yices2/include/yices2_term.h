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
#include "yices2_instance_ref.h"
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
  Yices2TermIter(term_t t, uint32_t p);
  Yices2TermIter(const Yices2TermIter & it);
  Yices2TermIter & operator=(const Yices2TermIter & it);
  void operator++() override;
  Term operator*() const override;
  TermIterBase * clone() const override;
  bool operator==(const Yices2TermIter & it) const;
  bool operator!=(const Yices2TermIter & it) const;

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
  // keeps Yices set up while the iterator can be used, even past its term
  // and solver
  Yices2InstanceRef instance;
  term_t term;
  uint32_t pos;
};

class Yices2Term : public AbsTerm
{
 public:
  Yices2Term(term_t t) : term(t) {};
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
  uint64_t to_int() const override;
  int64_t to_signed_int() const override;
  /* Iterators for traversing the children */
  TermIter begin() const override;
  TermIter end() const override;
  std::string print_value_as(SortKind sk) const override;

 protected:
  // keeps Yices set up while the term can be used, even past its solver
  Yices2InstanceRef instance;
  term_t term;

  friend class Yices2TermIter;

  friend class Yices2Solver;
};

}  // namespace smt
