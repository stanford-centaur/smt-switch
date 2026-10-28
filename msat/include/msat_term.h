/*********************                                                        */
/*! \file msat_term.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief MathSAT implementation of AbsTerm
**
**
**/

#pragma once

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>

#include "mathsat.h"
#include "term.h"

namespace smt {

// forward declaration
class MsatSolver;
class MsatInterpolatingSolver;

class MsatTermIter : public TermIterBase
{
 public:
  // TODO: consider making env const everywhere
  MsatTermIter(const std::shared_ptr<msat_env> & e,
               const msat_term t,
               uint32_t p);
  void operator++() override;
  Term operator*() const override;
  TermIterBase * clone() const override;
  bool operator==(const MsatTermIter & it) const;
  bool operator!=(const MsatTermIter & it) const;

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
  std::shared_ptr<msat_env> env;
  msat_term term;
  uint32_t pos;
};

class MsatTerm : public AbsTerm
{
 public:
  MsatTerm(const std::shared_ptr<msat_env> & e, msat_term t);
  MsatTerm(const std::shared_ptr<msat_env> & e, msat_decl d);
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
  /** Iterators for traversing the children
   */
  TermIter begin() const override;
  TermIter end() const override;
  std::string print_value_as(SortKind sk) const override;

  // Getters for solver-specific objects
  // for interacting with third-party MathSAT-specific software
  msat_term get_msat_term() const;
  msat_decl get_msat_decl() const;

 protected:
  // shared with the solver, so the environment lives as long as this term
  std::shared_ptr<msat_env> env;
  // whichever of term and decl is not wrapped stays null (invalid)
  msat_term term = { nullptr };
  msat_decl decl = { nullptr };
  bool is_uf = false;  ///< set to true if wrapping a msat_decl (e.g. an
                       ///< uninterpreted function)

  friend class MsatSolver;
  friend class MsatInterpolatingSolver;
};

}  // namespace smt
