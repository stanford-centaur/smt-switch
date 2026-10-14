/*********************                                                        */
/*! \file bitwuzla_sort.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bitwuzla implementation of AbsSort
**
**
**/

#pragma once

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>

#include "bitwuzla/cpp/bitwuzla.h"
#include "smt.h"

namespace smt {

// forward declaration
class BzlaSolver;

class BzlaSort : public AbsSort
{
 public:
  BzlaSort(const bitwuzla::Sort s,
           const std::shared_ptr<bitwuzla::TermManager> & tm);
  virtual ~BzlaSort();
  std::size_t hash() const override;
  std::uint64_t get_width() const override;
  Sort get_indexsort() const override;
  Sort get_elemsort() const override;
  SortVec get_domain_sorts() const override;
  Sort get_codomain_sort() const override;
  std::string get_uninterpreted_name() const override;
  std::size_t get_arity() const override;
  SortVec get_uninterpreted_param_sorts() const override;
  Datatype get_datatype() const override;
  bool compare(const Sort & s) const override;
  SortKind get_sort_kind() const override;

  // getters for solver-specific objects
  // for interacting with third-party Bitwuzla-specific software

  const bitwuzla::Sort get_bitwuzla_sort() const { return sort; };

 protected:
  // the term manager that owns sort, kept alive for as long as sort is
  // (declared first, so that sort is destroyed before it)
  const std::shared_ptr<bitwuzla::TermManager> tm;
  // objects from Bitwuzla API
  const bitwuzla::Sort sort;

  friend class BzlaSolver;
};

}  // namespace smt
