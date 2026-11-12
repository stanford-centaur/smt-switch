/*!
 * \file yices2_sort.h
 * \brief Yices2 implementation of AbsSort
 * \author Amalee Wilson
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_YICES2_SORT_H
#define SMT_SWITCH_YICES2_SORT_H

#include <yices_types.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/yices2_instance_ref.h"

namespace smt {

class Yices2Sort : public AbsSort
{
 public:
  /** A sort constructor has no type, only the macro id
   *  yices_type_constructor gave it: Yices2Sort(NULL_TYPE, false, id)
   */
  explicit Yices2Sort(type_t y_type,
                      bool is_fun = false,
                      std::int32_t constructor = -1);

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
  bool compare(const Sort & s) const override;
  SortKind get_sort_kind() const override;
  type_t get_ytype() const;

 protected:
  // keeps Yices set up while the sort can be used, even past its solver
  Yices2InstanceRef instance = {};
  type_t type;
  bool is_function;
  // the macro id of the sort constructor this sort is, or -1 if it is a type
  std::int32_t constructor_id;

  friend class Yices2Solver;
};

}  // namespace smt

#endif  // SMT_SWITCH_YICES2_SORT_H
