/*********************                                                        */
/*! \file cvc4_sort.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief CVC4 implementation of AbsSort
**
**
**/

#pragma once

#include <unordered_map>

#include "sort.h"

#include "api/cvc4cpp.h"
#include "api/cvc4cppkind.h"

namespace smt
{

  // forward declaration
  class CVC4Solver;

  class CVC4Sort : public AbsSort
  {
  public:
    CVC4Sort(::CVC4::api::Sort s) : sort(s) {};
    ~CVC4Sort() = default;
    std::string to_string() const override;
    std::size_t hash() const override;
    uint64_t get_width() const override;
    Sort get_indexsort() const override;
    Sort get_elemsort() const override;
    SortVec get_domain_sorts() const override;
    Sort get_codomain_sort() const override;
    std::string get_uninterpreted_name() const override;
    Datatype get_datatype() const override;
    size_t get_arity() const override;
    bool compare(const Sort) const override;
    SortKind get_sort_kind() const override;

   protected:
    ::CVC4::api::Sort sort;

    friend class CVC4Solver;

  };

}

