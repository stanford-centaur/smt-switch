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

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>

#include "bitwuzla/cpp/bitwuzla.h"
#include "bitwuzla_sort.h"
#include "smt_defs.h"
#include "sort.h"
#include "term.h"

namespace smt {

// forward declaration
class BzlaSolver;

class BzlaTermIter : public TermIterBase
{
 public:
  BzlaTermIter(bitwuzla::Term t,
               std::size_t i,
               const std::shared_ptr<bitwuzla::TermManager> & manager);
  void operator++() override;
  Term operator*() const override;
  TermIterBase * clone() const override;
  bool operator==(const BzlaTermIter & it) const;
  bool operator!=(const BzlaTermIter & it) const;

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
  // keeps the term manager alive for as long as terms is
  std::shared_ptr<bitwuzla::TermManager> tm;
  bitwuzla::Term terms;  // terms to iterate over (e.g. children)
  std::size_t idx;       // current idx of iteration
};

class BzlaTerm : public AbsTerm
{
 public:
  BzlaTerm(bitwuzla::Term n,
           const std::shared_ptr<bitwuzla::TermManager> & manager);
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
  std::uint64_t to_int() const override;
  std::int64_t to_signed_int() const override;
  /** Iterators for traversing the children
   */
  TermIter begin() const override;
  TermIter end() const override;
  std::string print_value_as(SortKind sk) const override;

  // getters for solver-specific objects
  // for interacting with third-party Bitwuzla-specific software

  const bitwuzla::Term get_bitwuzla_term() const { return term; };

 protected:
  // the term manager that owns term, kept alive for as long as term is
  // (declared first, so that term is destroyed before it)
  const std::shared_ptr<bitwuzla::TermManager> tm;
  // the actual API level node that is used
  const bitwuzla::Term term;

  friend class BzlaSolver;
  friend class BzlaInterpolatingSolver;
  friend class BzlaTermIter;
};

}  // namespace smt
