/*********************                                                        */
/*! \file yices2_term.h
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Yices2 implementation of AbsTerm
**
**
**/

#pragma once

#include <yices_types.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "smt_defs.h"
#include "sort.h"
#include "term.h"
#include "yices2_instance_ref.h"

namespace smt {

class Yices2Term : public AbsTerm
{
 public:
  explicit Yices2Term(term_t t);
  std::size_t hash() const override;
  std::size_t get_id() const override;
  bool compare(const Term & absterm) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  bool is_symbol() const override;
  bool is_param() const override;
  bool is_symbolic_const() const override;
  bool is_value() const override;
  virtual std::string to_string() const override;
  std::string get_constructor_name() const override;
  std::string get_param_name() const override;
  std::string get_selector_name() const override;
  std::string get_symbol_name() const override;
  uint64_t to_int() const override;
  int64_t to_signed_int() const override;
  std::string print_value_as(SortKind sk) const override;

 protected:
  std::size_t get_num_children() const override;
  Term get_child(std::size_t i) const override;

  // keeps Yices set up while the term can be used, even past its solver
  Yices2InstanceRef instance = {};
  term_t term;

  friend class Yices2Solver;
  friend class Yices2InterpolatingSolver;
};

}  // namespace smt
