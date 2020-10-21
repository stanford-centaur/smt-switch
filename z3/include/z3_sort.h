/*********************                                                        */
/*! \file z3_sort.h
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Z3 implementation of AbsSort
**
**
**/

#pragma once

#include "exceptions.h"
#include "sort.h"
#include "utils.h"

#include "z3++.h"

using namespace z3;
namespace smt {

// forward declaration
class Z3Solver;

class Z3Sort : public AbsSort
{
 public:
  // Non-functions
  Z3Sort(sort z3sort) : type(z3sort), is_function(false){};

  // Functions
  // Z3Sort(type_t y_type, bool is_fun) : type(y_type), is_function(is_fun){};

  ~Z3Sort() = default;
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
  SortKind get_sort_kind() const override;
  // type_t get_ytype() { return type; };

 protected:
  sort type;
  bool is_function;

  friend class Z3Solver;
};

}  // namespace smt
