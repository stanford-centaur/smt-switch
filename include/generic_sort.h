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

#include <functional>

#include "exceptions.h"
#include "generic_datatype.h"
#include "smt_defs.h"
#include "sort.h"

namespace smt {

class GenericDatatye;
/* Helper functions for creating generic sorts */
Sort make_uninterpreted_generic_sort(std::string name, uint64_t arity);
Sort make_uninterpreted_generic_sort(Sort sort_cons, const SortVec& sorts);
Sort make_generic_sort(SortKind sk);
Sort make_generic_sort(SortKind sk, uint64_t width);
Sort make_generic_sort(SortKind sk, Sort sort1);
Sort make_generic_sort(SortKind sk, Sort sort1, Sort sort2);
Sort make_generic_sort(SortKind sk, Sort sort1, Sort sort2, Sort sort3);
Sort make_generic_sort(SortKind sk, SortVec sorts);
Sort make_generic_sort(Datatype dt);
/* smtlib representation of sort kinds */
std::string to_smtlib(SortKind);

/** \class GenericSort
 *  An abstract class for generic Sorts
 */
class GenericSort : public AbsSort
{
 public:
  GenericSort(SortKind sk);
  // This second constructor is only for datatype sorts
  GenericSort(SortKind sk, std::string name_var);
  // ONly for placeholder sorts
  GenericSort(std::string name);
  virtual ~GenericSort();
  SortKind get_sort_kind() const override;
  bool compare(const Sort & s) const override;

  /** The following functions are 
   *   implemented by sub-classes 
   */

  uint64_t get_width() const override
  {
    throw NotImplementedException(
        "get_width not implemented by GenericSort");
  }

  size_t get_arity() const override
  {
    throw NotImplementedException(
        "get_width not implemented by GenericSort");
  }

  Sort get_indexsort() const override
  {
    throw NotImplementedException(
        "get_indexsort not implemented by GenericSort");
  }

  Sort get_elemsort() const override
  {
    throw NotImplementedException(
        "get_elemsort not implemented by GenericSort");
  }

  SortVec get_domain_sorts() const override
  {
    throw NotImplementedException(
        "get_domain_sorts not implemented by GenericSort");
  }

  Sort get_codomain_sort() const override
  {
    throw NotImplementedException(
        "get_codomain_sort not implemented by GenericSort");
  }

  std::string get_uninterpreted_name() const override
  {
    throw NotImplementedException(
        "get_uninterpreted_name not implemented by GenericSort");
  }

  std::vector<Sort> get_uninterpreted_param_sorts() const override 
  {
    throw NotImplementedException(
        "get_uninterpreted_param_sorts not implemented by GenericSort");
  }

  Datatype get_datatype() const override
  {
    throw NotImplementedException(
        "get_datatype not implemented by GenericSort");
  }
  
  // hash computed via std::string hash
  std::size_t hash() const override;

  // A string representation of a sort
  std::string to_string() const override;

  std::string get_base_name() const;

 protected:
  // internal function to compute
  // the string representation of a sort
  std::string compute_string() const;
  std::string base_name;
  // The underlying SortKind of the GenericSort
  SortKind sk;

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
  BVGenericSort(uint64_t width);
  ~BVGenericSort();

  uint64_t get_width() const override;

 protected:
  uint64_t width;
};

class ArrayGenericSort : public GenericSort
{
 public:
  ArrayGenericSort(Sort idxsort, Sort esort);
  ~ArrayGenericSort();

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
  ~FunctionGenericSort();

  SortVec get_domain_sorts() const override;
  Sort get_codomain_sort() const override;

 protected:
  SortVec domain_sorts;
  Sort codomain_sort;
};

class UninterpretedGenericSort : public GenericSort
{
 public:
  UninterpretedGenericSort(std::string n, uint64_t a);
  UninterpretedGenericSort(Sort sort_cons,
                           const SortVec & sorts);
  ~UninterpretedGenericSort();

  std::string get_uninterpreted_name() const override;
  size_t get_arity() const override;
  SortVec get_uninterpreted_param_sorts() const override;

 protected:
  std::string name;
  uint64_t arity;
  SortVec param_sorts;  
};

class GenericDatatypeSort : public GenericSort
{
 public:
  GenericDatatypeSort(const Datatype & dt);
  ~GenericDatatypeSort();
  std::string get_sort_name();
  Datatype get_datatype() const override;
  bool compare(const Sort & s) const override;
  std::string compute_string() const;
  std::string to_string() const override;

 protected:
  Datatype gdt;
};

}  // namespace smt
