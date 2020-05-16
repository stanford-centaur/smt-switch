/*********************                                                        */
/*! \file logging_sort.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class that wraps another Sort object and maintains the expected
**        SortKind and parameters (for solvers that alias sorts).
**
**/

#pragma once

#include "exceptions.h"
#include "smt_defs.h"
#include "sort.h"

namespace smt {

/* Helper functions for creating logging sorts */
// Sort s is the underlying sort
// all other sorts are LoggingSorts
Sort make_uninterpreted_logging_sort(Sort s, std::string name, uint64_t arity);
Sort make_logging_sort(SortKind sk, Sort s);
Sort make_logging_sort(SortKind sk, Sort s, uint64_t width);
Sort make_logging_sort(SortKind sk, Sort s, Sort sort1);
Sort make_logging_sort(SortKind sk, Sort s, Sort sort1, Sort sort2);
Sort make_logging_sort(SortKind sk, Sort s, Sort sort1, Sort sort2, Sort sort3);
Sort make_logging_sort(SortKind sk, Sort s, SortVec sorts);

/** \class LoggingSort
 *  An abstract class for logging created Sorts
 */
class LoggingSort : public AbsSort
{
 public:
  LoggingSort(SortKind sk, Sort s) : sk(sk), wrapped_sort(s) {}
  virtual ~LoggingSort(){};
  // implementations
  SortKind get_sort_kind() const override;
  bool compare(const Sort s) const override;
  // dispatch to underlying sort
  std::size_t hash() const override;

  // throw not implemented exception
  // for specific getters (will be
  // implemented by a subclass)
  uint64_t get_width() const override
  {
    throw NotImplementedException(
        "get_width not implemented by generic LoggingSort");
  }

  Sort get_indexsort() const override
  {
    throw NotImplementedException(
        "get_indexsort not implemented by generic LoggingSort");
  }

  Sort get_elemsort() const override
  {
    throw NotImplementedException(
        "get_elemsort not implemented by generic LoggingSort");
  }

  SortVec get_domain_sorts() const override
  {
    throw NotImplementedException(
        "get_domain_sorts not implemented by generic LoggingSort");
  }

  Sort get_codomain_sort() const override
  {
    throw NotImplementedException(
        "get_codomain_sort not implemented by generic LoggingSort");
  }

  std::string get_uninterpreted_name() const override
  {
    throw NotImplementedException(
        "get_uninterpreted_name not implemented by generic LoggingSort");
  }

 protected:
  SortKind sk;
  Sort wrapped_sort;

  // So LoggingSolver can access protected members:
  friend class LoggingSolver;
};

class BVLoggingSort : public LoggingSort
{
 public:
  BVLoggingSort(Sort s, uint64_t width);
  ~BVLoggingSort();

  typedef LoggingSort super;

  uint64_t get_width() const override;

 protected:
  uint64_t width;
};

class ArrayLoggingSort : public LoggingSort
{
 public:
  ArrayLoggingSort(Sort s, Sort idxsort, Sort esort);
  ~ArrayLoggingSort();

  typedef LoggingSort super;

  Sort get_indexsort() const override;
  Sort get_elemsort() const override;

 protected:
  Sort indexsort;
  Sort elemsort;
};

class FunctionLoggingSort : public LoggingSort
{
 public:
  FunctionLoggingSort(Sort s, SortVec sorts, Sort rsort);
  ~FunctionLoggingSort();

  typedef LoggingSort super;

  SortVec get_domain_sorts() const override;
  Sort get_codomain_sort() const override;

 protected:
  SortVec domain_sorts;
  Sort codomain_sort;
};

class UninterpretedLoggingSort : public LoggingSort
{
 public:
  UninterpretedLoggingSort(Sort s, std::string n, uint64_t a);
  ~UninterpretedLoggingSort();

  typedef LoggingSort super;

  std::string get_uninterpreted_name() const override;

 protected:
  std::string name;
  uint64_t arity;
};

}  // namespace smt
