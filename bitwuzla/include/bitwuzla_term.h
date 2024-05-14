/*********************                                                        */
/*! \file bitwuzla_term.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bitwuzla implementation of AbsTerm
**
**
**/

#pragma once

#include <vector>

#include "bitwuzla/cpp/bitwuzla.h"
#include "bitwuzla_sort.h"
#include "term.h"
#include "utils.h"

namespace smt {

// forward declaration
class BzlaSolver;

class BzlaTermIter : public TermIterBase
{
 public:
  BzlaTermIter(bitwuzla::Term terms, size_t idx)
      : terms(terms), idx(idx)
  {
  }
  BzlaTermIter(const BzlaTermIter & it)
  {
    terms = it.terms;
    idx = it.idx;
  };
  ~BzlaTermIter(){};
  BzlaTermIter & operator=(const BzlaTermIter & it);
  void operator++() override;
  const Term operator*() override;
  TermIterBase * clone() const override;
  bool operator==(const BzlaTermIter & it);
  bool operator!=(const BzlaTermIter & it);

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
  bitwuzla::Term terms;  // terms to iterate over (e.g. children)
  size_t idx;             // current idx of iteration
};

class BzlaTerm : public AbsTerm
{
 public:
  BzlaTerm(const bitwuzla::Term n);
  ~BzlaTerm();
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
  /** Iterators for traversing the children
   */
  TermIter begin() override;
  TermIter end() override;
  std::string print_value_as(SortKind sk) override;

  // getters for solver-specific objects
  // for interacting with third-party Bitwuzla-specific software

  // const bitwuzla::Term * get_bitwuzla_term() const { return term; };

 protected:
  // the actual API level node that is used
  const bitwuzla::Term term;

  // helpers
  /** Calls boolector's to_string with either btor or smt2 format*/
  std::string to_string_formatted(const char * fmt) const;

  friend class BzlaSolver;
  friend class BzlaTermIter;
};

}  // namespace smt
