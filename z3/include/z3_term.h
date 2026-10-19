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

#pragma once

#include <cstdint>
#include <memory>
#include <vector>

#include "term.h"
#include "utils.h"
#include "z3++.h"
#include "z3_sort.h"

namespace smt {

// forward declaration
class Z3Solver;

class Z3TermIter : public TermIterBase
{
 public:
  Z3TermIter(const std::shared_ptr<context> & c,
             expr t,
             uint32_t p,
             bool nt = false);
  Z3TermIter(const Z3TermIter & it);
  Z3TermIter & operator=(const Z3TermIter & it);
  void operator++() override;
  Term operator*() const override;
  TermIterBase * clone() const override;
  bool operator==(const Z3TermIter & it) const;
  bool operator!=(const Z3TermIter & it) const;

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
  // declared before term, so that term is released while the context lives
  std::shared_ptr<context> ctx;
  expr term;
  uint32_t pos;
  bool null_term;  ///< set to true if the term is null (no iteration)
};

class Z3Term : public AbsTerm
{
 public:
  // Non-functions
  Z3Term(const std::shared_ptr<context> & c, expr t);
  // Parameter -- Z3 doesn't distinguish until it's bound
  // so we have to keep track of this extra info
  // if no bool is passed, assume it's not a parameter
  Z3Term(const std::shared_ptr<context> & c, expr t, bool param);
  // Functions
  Z3Term(const std::shared_ptr<context> & c, func_decl zfunc);
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
  uint64_t to_int() const override;
  int64_t to_signed_int() const override;
  /* Iterators for traversing the children */
  TermIter begin() const override;
  TermIter end() const override;
  std::string print_value_as(SortKind sk) const override;

  // getters for solver-specific objects (EXPERTS only)
  expr get_z3_expr() const;
  func_decl get_z3_func_decl() const;

 protected:
  // shared with the solver, so the context lives as long as this term, and
  // declared first, so that term and z_func are released while it does
  std::shared_ptr<context> ctx;
  expr term;
  func_decl z_func;
  bool is_function;
  bool is_parameter;

  friend class Z3Solver;
  friend class Z3TermIter;
};

}  // namespace smt
