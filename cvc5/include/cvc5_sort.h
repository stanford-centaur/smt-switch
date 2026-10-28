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

#include <cvc5/cvc5.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "smt_defs.h"
#include "sort.h"

namespace smt {

class Cvc5Sort : public AbsSort
{
 public:
  explicit Cvc5Sort(::cvc5::Sort s);
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

  // Getters for solver-specific objects
  // for interacting with third-party cvc5-specific software
  ::cvc5::Sort get_cvc5_sort() const;
  /** The datatype, as get_datatype gives it, without wrapping it
   *  @throws IncorrectUsageException if the sort has no datatype
   */
  ::cvc5::Datatype get_cvc5_datatype() const;

 protected:
  ::cvc5::Sort sort;

  friend class Cvc5Solver;
};

}  // namespace smt
