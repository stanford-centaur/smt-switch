/*********************                                                        */
/*! \file z3_term.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Lindsey Stuntz
 ** This file is part of the smt-switch project.
 ** Copyright (c) 2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Z3 implementation of AbsTerm
 **
 **
 **/
#ifndef SMT_SWITCH_Z3_TERM_H
#define SMT_SWITCH_Z3_TERM_H

#include <z3++.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>

#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/z3_context.h"

namespace smt {

class Z3Term : public AbsTerm
{
 public:
  // Non-functions
  Z3Term(const std::shared_ptr<Z3Context> & c, z3::expr t);
  // Functions
  Z3Term(const std::shared_ptr<Z3Context> & c, z3::func_decl zfunc);
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
  bool to_bool() const override;
  std::string print_value_as(SortKind sk) const override;

  // getters for solver-specific objects (EXPERTS only)
  z3::expr get_z3_expr() const;
  z3::func_decl get_z3_func_decl() const;

 protected:
  std::size_t get_num_children() const override;
  Term get_child(std::size_t i) const override;

  // shared with the solver, so the context lives as long as this term, and
  // declared first, so that term and z_func are released while it does
  std::shared_ptr<Z3Context> ctx;
  z3::expr term;
  z3::func_decl z_func;
  bool is_function = false;

  friend class Z3Solver;
};

}  // namespace smt

#endif  // SMT_SWITCH_Z3_TERM_H
