/*********************                                                        */
/*! \file generic_sort.h
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class that represents a sort in generic solvers
**
**
**/

#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <vector>

#include "exceptions.h"
#include "smt_defs.h"
#include "sort.h"

namespace smt {

/** \class GenericSort
 *  An abstract class for generic Sorts
 */
class GenericSort : public AbsSort
{
 public:
  explicit GenericSort(SortKind k);
  // Only for placeholder sorts used for datatypes. name
  // should be the name of the datatype.
  explicit GenericSort(std::string name);
  SortKind get_sort_kind() const override;
  bool compare(const Sort & s) const override;

  /* The following functions are implemented by the sub-classes whose kind
   * has them, so reaching one here means the sort's kind does not */

  std::uint64_t get_width() const override;
  std::size_t get_arity() const override;
  Sort get_indexsort() const override;
  Sort get_elemsort() const override;
  SortVec get_domain_sorts() const override;
  Sort get_codomain_sort() const override;
  std::string get_uninterpreted_name() const override;
  std::vector<Sort> get_uninterpreted_param_sorts() const override;
  Datatype get_datatype() const override;

  // hash computed via std::string hash
  std::size_t hash() const override;

  // A string representation of a sort
  std::string to_string() const override;

 protected:
  // internal function to compute
  // the string representation of a sort
  virtual std::string compute_string() const;
  // The underlying SortKind of the GenericSort
  SortKind sk;

  // Set only by GenericSort(std::string), which builds a DATATYPE sort
  // standing in for a datatype whose own sort does not exist yet. Empty for
  // every other sort, including GenericDatatypeSort, which has a real
  // datatype to ask.
  std::string datatype_name;

  // strings hash function, to be used for hash()
  std::hash<std::string> str_hash;

  // So GenericSolver can access protected members:
  friend class GenericSolver;
};

/**
 * sub-classes of specific kinds of sorts
 */

class BVGenericSort : public GenericSort
{
 public:
  explicit BVGenericSort(std::uint64_t w);

  std::uint64_t get_width() const override;

 protected:
  std::uint64_t width;
};

class ArrayGenericSort : public GenericSort
{
 public:
  ArrayGenericSort(Sort idxsort, Sort esort);

  Sort get_indexsort() const override;
  Sort get_elemsort() const override;

 protected:
  Sort indexsort;
  Sort elemsort;
};

class FunctionGenericSort : public GenericSort
{
 public:
  FunctionGenericSort(SortVec sorts, Sort rsort);

  SortVec get_domain_sorts() const override;
  Sort get_codomain_sort() const override;

 protected:
  SortVec domain_sorts;
  Sort codomain_sort;
};

class UninterpretedGenericSort : public GenericSort
{
 public:
  UninterpretedGenericSort(std::string n, std::uint64_t a);
  UninterpretedGenericSort(Sort sort_cons, const SortVec & sorts);

  std::string get_uninterpreted_name() const override;
  std::size_t get_arity() const override;
  SortVec get_uninterpreted_param_sorts() const override;

 protected:
  std::string name;
  std::uint64_t arity;
  SortVec param_sorts;
};

class GenericDatatypeSort : public GenericSort
{
 public:
  explicit GenericDatatypeSort(const Datatype & dt);
  Datatype get_datatype() const override;
  bool compare(const Sort & s) const override;
  std::string compute_string() const override;
  std::string to_string() const override;

 protected:
  Datatype gdt;
};

/* This class defines a sort class that can represent constructors,
   selectors, and testers. Sorts of this variety are primarily used to
   build generic terms representing constructors, selectors, and testers.
 */
class DatatypeComponentSort : public GenericSort
{
 public:
  DatatypeComponentSort(SortKind k, std::string n, Sort dt);
  bool compare(const Sort & s) const override;
  std::size_t hash() const override;
  std::string compute_string() const override;
  std::string to_string() const override;
  SortVec get_domain_sorts() const override;
  Sort get_codomain_sort() const override;
  void set_selector_sort(Sort new_selector_sort);
  int get_num_selectors() const;

 protected:
  std::string name;
  Sort dt_sort;
  Sort selector_sort;
};

}  // namespace smt
