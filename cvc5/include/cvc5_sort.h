/*********************                                                        */
/*! \file cvc5_sort.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief cvc5 implementation of AbsSort
**
**
**/

#pragma once

#include <unordered_map>

#include "api/cpp/cvc5.h"
#include "api/cpp/cvc5_kind.h"
#include "sort.h"

namespace smt {

// forward declaration
class Cvc5Solver;

class Cvc5Sort : public AbsSort
{
 public:
  Cvc5Sort(::cvc5::api::Sort s) : sort(s){};
  ~Cvc5Sort() = default;
  std::string to_string() const override;
  std::size_t hash() const override;
  uint64_t get_width() const override;
  Sort get_indexsort() const override;
  Sort get_elemsort() const override;
  SortVec get_domain_sorts() const override;
  Sort get_codomain_sort() const override;
  std::string get_uninterpreted_name() const override;
  size_t get_arity() const override;
  SortVec get_uninterpreted_param_sorts() const override;
  Datatype get_datatype() const override;
  bool compare(const Sort &) const override;
  SortKind get_sort_kind() const override;

  // getters for solver-specific objects
  // for interacting with third-party cvc5-specific software
  ::cvc5::api::Sort get_cvc5_sort() const { return sort; };

 protected:
  ::cvc5::api::Sort sort;

  friend class Cvc5Solver;
};

}  // namespace smt
