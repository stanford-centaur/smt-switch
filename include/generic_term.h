/*********************                                                        */
/*! \file generic_term.h
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class that represents a term with
**        Op and children.
**
**/

#pragma once

#include <functional>

#include "ops.h"
#include "smt_defs.h"
#include "term.h"

namespace smt {

class GenericTerm : public AbsTerm
{
 public:
  // General constructor
  GenericTerm(Sort s, Op o, TermVec c, std::string r);
  // this one is for making symbols
  // if passed with true, sets is_sym true
  // otherwise sets is_param true
  // only symbols and parameters have names
  // symbols are "free" uninterpreted constants and functions
  // params are bound variables
  GenericTerm(Sort s, Op o, TermVec c, std::string r, bool is_sym);
  virtual ~GenericTerm();

  /** Returns true iff the term AND sort are equivalent
   *  @param t the term to compare with (assumed to be GenericTerm)
   *  @return true iff the term and sort match t
   */
  bool compare(const Term & t) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  std::size_t get_id() const override;
  std::string to_string() override;
  std::size_t hash() const override;
  bool is_value() const override;
  uint64_t to_int() const override;
  std::string print_value_as(SortKind sk) override;
  bool is_symbol() const override;
  bool is_param() const override;
  bool is_symbolic_const() const override;
  TermIter begin() override;
  TermIter end() override;
  TermVec get_children();

 protected:
  std::string compute_string() const;

  /**
   * A hash function for strings,
   * to be used to compute the hash of the term.
   */
  std::hash<std::string> str_hash;

  // The term's sort
  Sort sort;

  /**
   * The top-most operator of the term.
   * null op if there isn't any op.
   */
  Op op;

  // Immediate children of the term
  TermVec children;

  // A string representation of the term
  std::string repr;

  // is this a symbolic constant
  bool is_sym;

  // is this a variable
  bool is_par;

  // So GenericSolver can access protected members:
  friend class GenericSolver;
};

class GenericTermIter : public TermIterBase
{
 public:
  GenericTermIter(TermVec::iterator i);
  GenericTermIter(const GenericTermIter & lit);
  ~GenericTermIter();
  TermIterBase * clone() const override;

  GenericTermIter & operator=(const GenericTermIter & lit);
  void operator++() override;
  const Term operator*() override;
  bool operator==(const GenericTermIter & lit);
  bool operator!=(const GenericTermIter & lit);

 protected:
  bool equal(const TermIterBase & other) const override;
  TermVec::iterator it;
};

}  // namespace smt
