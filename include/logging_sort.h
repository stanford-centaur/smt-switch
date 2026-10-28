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

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>

#include "logging_datatype.h"
#include "smt_defs.h"
#include "sort.h"

namespace smt {

/* Helper functions for creating logging sorts */
// Sort s is the underlying sort
// all other sorts are LoggingSorts
Sort make_uninterpreted_logging_sort(Sort s,
                                     std::string name,
                                     std::uint64_t arity);
Sort make_uninterpreted_logging_sort(Sort s,
                                     std::string name,
                                     const SortVec & sorts);
Sort make_logging_sort(SortKind sk, Sort s);
Sort make_logging_sort(SortKind sk, Sort s, std::uint64_t width);
Sort make_logging_sort(SortKind sk, Sort s, SortVec sorts);

/** \class LoggingSort
 *  An abstract class for logging created Sorts
 */
class LoggingSort : public AbsSort
{
 public:
  LoggingSort(SortKind k, Sort s);
  // implementations
  SortKind get_sort_kind() const override;
  bool compare(const Sort & s) const override;
  // dispatch to underlying sort
  std::size_t hash() const override;

  // the specific getters are implemented by the subclasses whose kind has
  // them, so reaching one here means the sort's kind does not
  std::uint64_t get_width() const override;
  Sort get_indexsort() const override;
  Sort get_elemsort() const override;
  SortVec get_domain_sorts() const override;
  Sort get_codomain_sort() const override;
  std::string get_uninterpreted_name() const override;
  std::size_t get_arity() const override;
  SortVec get_uninterpreted_param_sorts() const override;
  Datatype get_datatype() const override;

 protected:
  SortKind sk;
  Sort wrapped_sort;

  // So LoggingSolver can access protected members:
  friend class LoggingSolver;
};

class BVLoggingSort : public LoggingSort
{
 public:
  BVLoggingSort(Sort s, std::uint64_t w);

  typedef LoggingSort super;

  std::uint64_t get_width() const override;

 protected:
  std::uint64_t width;
};

class ArrayLoggingSort : public LoggingSort
{
 public:
  ArrayLoggingSort(Sort s, Sort idxsort, Sort esort);

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
  UninterpretedLoggingSort(Sort s, std::string n, std::uint64_t a);
  UninterpretedLoggingSort(Sort s,
                           std::string n,
                           std::uint64_t a,
                           const SortVec & sorts);

  typedef LoggingSort super;

  std::string get_uninterpreted_name() const override;
  std::size_t get_arity() const override;
  SortVec get_uninterpreted_param_sorts() const override;

 protected:
  std::string name;
  std::uint64_t arity;
  SortVec param_sorts;
};

class DatatypeLoggingSort : public LoggingSort
{
 public:
  DatatypeLoggingSort(Sort s, std::shared_ptr<LoggingDatatypeDecl> d);

  typedef LoggingSort super;

  Datatype get_datatype() const override;

 protected:
  /** the declaration it was made from, which names each selector's sort */
  std::shared_ptr<LoggingDatatypeDecl> decl;

  friend class LoggingSolver;
};

/** The sort of a datatype's constructor, selector or tester term */
class DatatypeComponentLoggingSort : public LoggingSort
{
 public:
  DatatypeComponentLoggingSort(SortKind k,
                               Sort s,
                               SortVec domain,
                               Sort codomain);

  typedef LoggingSort super;

  SortVec get_domain_sorts() const override;
  Sort get_codomain_sort() const override;

 protected:
  SortVec domain_sorts;
  Sort codomain_sort;
};

}  // namespace smt
