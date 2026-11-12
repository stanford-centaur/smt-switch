/*!
 * \file generic_sort.h
 * \brief Class that represents a sort in generic solvers
 * \author Yoni Zohar
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_GENERIC_SORT_H
#define SMT_SWITCH_GENERIC_SORT_H

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>

#include "smt-switch/generic_datatype.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"

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
  Sort get_indexsort() const override;
  Sort get_elemsort() const override;
  SortVec get_domain_sorts() const override;
  Sort get_codomain_sort() const override;
  std::string get_uninterpreted_name() const override;
  std::size_t get_arity() const override;
  Sort get_uninterpreted_constructor() const override;
  std::vector<Sort> get_uninterpreted_param_sorts() const override;
  Datatype get_datatype() const override;
  /** The datatype, as get_datatype gives it, without casting it down
   *  @throws IncorrectUsageException if the sort has no datatype
   */
  virtual std::shared_ptr<GenericDatatype> get_generic_datatype() const;

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
  std::string datatype_name = "";

  // strings hash function, to be used for hash()
  std::hash<std::string> str_hash = {};

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
  Sort get_uninterpreted_constructor() const override;
  SortVec get_uninterpreted_param_sorts() const override;

 protected:
  std::string name;
  std::uint64_t arity;
  Sort constructor = nullptr;
  SortVec param_sorts = {};
};

class GenericDatatypeSort : public GenericSort
{
 public:
  explicit GenericDatatypeSort(std::shared_ptr<GenericDatatype> dt);
  std::shared_ptr<GenericDatatype> get_generic_datatype() const override;
  bool compare(const Sort & s) const override;
  std::string compute_string() const override;
  std::string to_string() const override;

 protected:
  std::shared_ptr<GenericDatatype> gdt;
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
  /** @return the name a constructor or selector was declared with, or that
   *  of the constructor a tester tests
   */
  std::string get_name() const;

 protected:
  std::string name;
  std::shared_ptr<GenericSort> dt_sort;
  Sort selector_sort = nullptr;
};

}  // namespace smt

#endif  // SMT_SWITCH_GENERIC_SORT_H
