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

#include <cstdint>
#include <memory>
#include <vector>

#include "boolector.h"
extern "C" {
#include "btorcore.h"
#include "btornode.h"
#include "utils/btornodeiter.h"
}

#include "boolector_sort.h"
#include "term.h"
#include "utils.h"

namespace smt {

// forward declaration
class BoolectorSolver;

// helpers
Op lookup_op(Btor * btor, BoolectorNode * n);

class BoolectorTermIter : public TermIterBase
{
 public:
  // IMPORTANT: The correctness of this code depends on the array e being of
  // size 3
  BoolectorTermIter(const std::shared_ptr<Btor> & b,
                    std::vector<BtorNode *> c,
                    int64_t i);
  BoolectorTermIter(const BoolectorTermIter & it);
  ~BoolectorTermIter() override;
  BoolectorTermIter & operator=(const BoolectorTermIter & it);
  void operator++() override;
  Term operator*() const override;
  TermIterBase * clone() const override;
  bool operator==(const BoolectorTermIter & it) const;
  bool operator!=(const BoolectorTermIter & it) const;

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
  // keeps the instance alive for as long as this object is
  std::shared_ptr<Btor> btor;
  // this object holds a reference to each, so they stay alive after the
  // term they came from is gone
  std::vector<BtorNode *> children;
  int64_t idx;
};

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
  uint64_t to_int() const override;
  int64_t to_signed_int() const override;
  /** Iterators for traversing the children
   */
  TermIter begin() const override;
  TermIter end() const override;
  std::string print_value_as(SortKind sk) const override;

  // getters for solver-specific objects
  // for interacting with third-party Boolector-specific software

  BoolectorNode * get_btor_node() const { return node; };

 protected:
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
  bool negated;
  // for iterating args nodes
  mutable BtorArgsIterator ait;
  // for storing nodes before iterating
  mutable std::vector<BtorNode *> children;
  // flag that's set to true if children have already been gathered
  // not straightforward to just rely on number of children / arity
  // because boolector term representation isn't a perfect match
  // for the smt-switch abstract interface
  mutable bool children_cached_ =
      false;  ///< set to true if children have already been gathered

  // helpers
  bool is_const_array() const;
  void collect_children() const;

  friend class BoolectorSolver;
  friend class BoolectorTermIter;
};

}  // namespace smt
