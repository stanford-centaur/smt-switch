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

#include <vector>

#include "boolector.h"
extern "C" {
#include "btorcore.h"
#include "btornode.h"
#include "utils/btornodeiter.h"
}

#include "term.h"
#include "utils.h"

#include "boolector_sort.h"

namespace smt {

// forward declaration
class BoolectorSolver;

// helpers
Op lookup_op(Btor * btor, BoolectorNode * n);

class BoolectorTermIter : public TermIterBase
{
 public:
  // IMPORTANT: The correctness of this code depends on the array e being of size 3
  BoolectorTermIter(Btor * btor, std::vector<BtorNode *> c, int64_t idx)
      : btor(btor), children(c), idx(idx)
  {
  }
  BoolectorTermIter(const BoolectorTermIter & it)
  {
    btor = it.btor;
    children = it.children;
    idx = it.idx;
  };
  ~BoolectorTermIter(){};
  BoolectorTermIter & operator=(const BoolectorTermIter & it);
  void operator++() override;
  const Term operator*() override;
  TermIterBase * clone() const override;
  bool operator==(const BoolectorTermIter & it);
  bool operator!=(const BoolectorTermIter & it);

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
  Btor * btor;
  std::vector<BtorNode *> children;
  int64_t idx;
};

class BoolectorTerm : public AbsTerm
{
 public:
  BoolectorTerm(Btor * b, BoolectorNode * n);
  ~BoolectorTerm();
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
  /** Iterators for traversing the children
   */
  TermIter begin() override;
  TermIter end() override;
  std::string print_value_as(SortKind sk) override;

 protected:
  Btor * btor;
  // the actual API level node that is used
  BoolectorNode * node;
  // the real address of the boolector node
  // allows us to look up:
  //   kind: for retrieving operator
  //   e:    for getting children
  BtorNode * bn;
  // true iff the node is negated
  bool negated;
  // for iterating args nodes
  BtorArgsIterator ait;
  // for storing nodes before iterating
  std::vector<BtorNode *> children;

  // helpers
  bool is_const_array() const;

  friend class BoolectorSolver;
  friend class BoolectorTermIter;
};

}  // namespace smt

