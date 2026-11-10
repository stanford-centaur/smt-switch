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

#include <bitwuzla/cpp/bitwuzla.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>

#include "bitwuzla_term_manager.h"
#include "ops.h"
#include "smt_defs.h"
#include "sort.h"
#include "term.h"

namespace smt {

class BzlaTerm : public AbsTerm
{
 public:
  BzlaTerm(bitwuzla::Term n, const std::shared_ptr<BzlaTermManager> & manager);
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
  std::string get_constructor_name() const override;
  std::string get_param_name() const override;
  std::string get_selector_name() const override;
  std::string get_symbol_name() const override;
  std::uint64_t to_int() const override;
  std::int64_t to_signed_int() const override;
  bool to_bool() const override;
  std::string print_value_as(SortKind sk) const override;

  // Getters for solver-specific objects
  // for interacting with third-party Bitwuzla-specific software

  const bitwuzla::Term get_bitwuzla_term() const;

 protected:
  std::size_t get_num_children() const override;
  Term get_child(std::size_t i) const override;

  // the term manager that owns term, kept alive for as long as term is
  // (declared first, so that term is destroyed before it)
  const std::shared_ptr<BzlaTermManager> tm;
  // the actual API level node that is used
  const bitwuzla::Term term;

  friend class BzlaSolver;
  friend class BzlaInterpolatingSolver;
};

/** The Bitwuzla kind of the applications of po
 *  @throws NotImplementedException for an operator Bitwuzla does not support
 */
bitwuzla::Kind to_bitwuzla_kind(PrimOp po);

/** The PrimOp of the applications of kind
 *  @throws NotImplementedException for a kind that no PrimOp stands for
 */
PrimOp to_primop(bitwuzla::Kind kind);

}  // namespace smt
