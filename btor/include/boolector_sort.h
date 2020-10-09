/*********************                                                        */
/*! \file boolector_sort.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Boolector implementation of AbsSort
**
**
**/

#pragma once

#include "exceptions.h"
#include "sort.h"
#include "utils.h"

#include "boolector.h"

namespace smt {

// forward declaration
class BoolectorSolver;

class BoolectorSortBase : public AbsSort
{
 public:
  BoolectorSortBase(SortKind sk, Btor * b, BoolectorSort s)
      : btor(b), sort(s), sk(sk){};
  virtual ~BoolectorSortBase();
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
  bool compare(const Sort s) const override;
  SortKind get_sort_kind() const override { return sk; };

 protected:
  Btor * btor;
  BoolectorSort sort;
  SortKind sk;

  friend class BoolectorSolver;
};

/** The Boolector C API doesn't support querying sorts for the index sort
    of an array sort, etc...
    (in Boolector asking for the index is done on a node, i.e. Term, rather than
   a sort) Thus, we need to track some extra information for implementing
   AbsSort. To make this simpler, we have unique classes for each sort.
 */

class BoolectorBVSort : public BoolectorSortBase
{
 public:
  BoolectorBVSort(Btor * b, BoolectorSort s, uint64_t w)
      : BoolectorSortBase(BV, b, s), width(w){};
  uint64_t get_width() const override { return width; };

 protected:
  // bit-vector width
  // Note: we need to store this in addition to the BoolectorSort
  //       because in Boolector the width is retrieved from a node not a sort
  unsigned width;

  friend class BoolectorSolver;
};

class BoolectorArraySort : public BoolectorSortBase
{
 public:
  BoolectorArraySort(Btor * b, BoolectorSort s, Sort is, Sort es)
    : BoolectorSortBase(ARRAY, b, s), indexsort(is), elemsort(es) {};
  Sort get_indexsort() const override { return indexsort; };
  Sort get_elemsort() const override { return elemsort; };

 protected:
  Sort indexsort;
  Sort elemsort;

  friend class BoolectorSolver;
};

class BoolectorUFSort : public BoolectorSortBase
{
 public:
  BoolectorUFSort(Btor * b, BoolectorSort s, SortVec sorts, Sort sort)
      : BoolectorSortBase(FUNCTION, b, s),
        domain_sorts(sorts),
        codomain_sort(sort){};
  SortVec get_domain_sorts() const override { return domain_sorts; };
  Sort get_codomain_sort() const override { return codomain_sort; };

 protected:
  SortVec domain_sorts;
  Sort codomain_sort;

  friend class BoolectorSolver;
};
}  // namespace smt

