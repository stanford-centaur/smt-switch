/*!
 * \file z3_sort.h
 * \brief Z3 implementation of AbsSort
 * \author Lindsey Stuntz
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_Z3_SORT_H
#define SMT_SWITCH_Z3_SORT_H

#include <z3++.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>

#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/z3_context.h"

namespace smt {

class Z3Sort : public AbsSort
{
 public:
  // Non-functions
  Z3Sort(const std::shared_ptr<Z3Context> & c, z3::sort z3sort);

  // Functions
  Z3Sort(const std::shared_ptr<Z3Context> & c, z3::func_decl zfunc);

  // Sort constructors, which Z3's API lacks, by their name and arity
  Z3Sort(const std::shared_ptr<Z3Context> & c,
         std::string name,
         std::uint64_t arity);

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

  // getters for solver-specific objects (EXPERTS only)
  z3::sort get_z3_type() const;
  /** The sort, as get_datatype wraps it, once checked to be a datatype
   *  @throws IncorrectUsageException if the sort has no datatype
   */
  z3::sort get_z3_datatype() const;

 protected:
  // shared with the solver, so the context lives as long as this sort, and
  // declared first, so that type and z_func are released while it does
  std::shared_ptr<Z3Context> ctx;
  z3::sort type;
  z3::func_decl z_func;
  bool is_function = false;
  // a sort constructor's name and arity, when the sort is one
  bool is_constructor = false;
  std::string constructor_name = "";
  std::uint64_t constructor_arity = 0;

  friend class Z3Solver;
};

}  // namespace smt

#endif  // SMT_SWITCH_Z3_SORT_H
