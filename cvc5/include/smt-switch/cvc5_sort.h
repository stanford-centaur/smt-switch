/*!
 * \file cvc5_sort.h
 * \brief cvc5 implementation of AbsSort
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_CVC5_SORT_H
#define SMT_SWITCH_CVC5_SORT_H

#include <cvc5/cvc5.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"

namespace smt {

class Cvc5Sort : public AbsSort
{
 public:
  explicit Cvc5Sort(cvc5::Sort s);
  std::string to_string() const override;
  std::size_t hash() const override;
  std::uint64_t get_width() const override;
  Sort get_indexsort() const override;
  Sort get_elemsort() const override;
  SortVec get_domain_sorts() const override;
  Sort get_codomain_sort() const override;
  std::string get_uninterpreted_name() const override;
  std::size_t get_arity() const override;
  Sort get_uninterpreted_constructor() const override;
  SortVec get_uninterpreted_param_sorts() const override;
  Datatype get_datatype() const override;
  bool compare(const Sort &) const override;
  SortKind get_sort_kind() const override;

  // Getters for solver-specific objects
  // for interacting with third-party cvc5-specific software
  cvc5::Sort get_cvc5_sort() const;
  /** The datatype, as get_datatype gives it, without wrapping it
   *  @throws IncorrectUsageException if the sort has no datatype
   */
  cvc5::Datatype get_cvc5_datatype() const;

 protected:
  cvc5::Sort sort;

  friend class Cvc5Solver;
};

}  // namespace smt

#endif  // SMT_SWITCH_CVC5_SORT_H
