/*********************                                                        */
/*! \file boolector_term.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Boolector implementation of AbsTerm
**
**
**/

#pragma once

#include <btortypes.h>

extern "C" {
#include <btorcore.h>
#include <btornode.h>
#include <utils/btornodeiter.h>
}

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "ops.h"
#include "smt_defs.h"
#include "sort.h"
#include "term.h"

namespace smt {

// helpers
Op lookup_op(Btor * btor, BoolectorNode * n);

class BoolectorTerm : public AbsTerm
{
 public:
  BoolectorTerm(const std::shared_ptr<Btor> & b, BoolectorNode * n);
  ~BoolectorTerm() override;
  // the destructor releases node, so a copy would release it twice
  BoolectorTerm(const BoolectorTerm &) = delete;
  BoolectorTerm & operator=(const BoolectorTerm &) = delete;
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
  std::string get_param_name() const override;
  std::string get_symbol_name() const override;
  uint64_t to_int() const override;
  int64_t to_signed_int() const override;
  std::string print_value_as(SortKind sk) const override;

  // Getters for solver-specific objects
  // for interacting with third-party Boolector-specific software

  BoolectorNode * get_btor_node() const;

 protected:
  std::size_t get_num_children() const override;
  Term get_child(std::size_t i) const override;

  // keeps the instance alive for as long as this object is
  std::shared_ptr<Btor> btor;
  // the actual API level node that is used
  BoolectorNode * node;
  // the real address of the boolector node
  // allows us to look up:
  //   kind: for retrieving operator
  //   e:    for getting children
  mutable BtorNode * bn;
  // true iff the node is negated
  bool negated = false;
  // true iff the node was made as a symbol, fixed at construction because
  // Boolector overwrites the kind of a symbol it substitutes
  bool symbol = false;
  // for iterating args nodes
  mutable BtorArgsIterator ait = {};
  // for storing nodes before iterating; this object holds a reference to
  // each, so they stay alive while they are listed
  mutable std::vector<BtorNode *> children = {};
  // flag that's set to true if children have already been gathered
  // not straightforward to just rely on number of children / arity
  // because boolector term representation isn't a perfect match
  // for the smt-switch abstract interface
  mutable bool children_cached_ = false;

  // helpers
  bool is_const_array() const;
  void collect_children() const;
  // releases and clears children
  void release_children() const;

  friend class BoolectorSolver;
};

}  // namespace smt
