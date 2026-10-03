/*********************                                                        */
/*! \file boolector_solver.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Boolector implementation of AbsSmtSolver
**
**
**/

#pragma once

#include <cassert>
#include <chrono>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_set>
#include <vector>

#include "boolector_extensions.h"
#include "boolector_sort.h"
#include "boolector_term.h"
#include "exceptions.h"
#include "result.h"
#include "smt.h"
#include "sort.h"

namespace smt {
/**
   Boolector Solver
 */
class BoolectorSolver : public AbsSmtSolver
{
 public:
  // might have to use std::unique_ptr<Btor>(boolector_new) and move it?
  BoolectorSolver();
  BoolectorSolver(const BoolectorSolver &) = delete;
  BoolectorSolver & operator=(const BoolectorSolver &) = delete;
  ~BoolectorSolver()
  {
    // need to destruct all stored terms in the symbol_table
    symbol_table.clear();
    boolector_delete(btor);
  };
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  // Overriding check_sat_assuming hides the AbsSmtSolver template that
  // takes any range of Terms, so name it back in.
  using AbsSmtSolver::check_sat_assuming;
  Result check_sat_assuming(const TermVec & assumptions) override;
  void push(uint64_t num = 1) override;
  void pop(uint64_t num = 1) override;
  uint64_t get_context_level() const override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) override;

  // The datatype methods are left to AbsSmtSolver, whose defaults throw.
  // Declaring make_sort here at all would hide AbsSmtSolver's own overloads
  // from lookup on this type, so name them back in.
  using AbsSmtSolver::make_sort;
  Sort make_sort(const std::string name, uint64_t arity) const override;
  Sort make_sort(SortKind sk) const override;
  Sort make_sort(SortKind sk, uint64_t size) const override;
  Sort make_sort(SortKind sk, const SortVec & sorts) const override;

  // AbsSmtSolver's string-value overloads are not declared here, and a
  // declaration of the name would otherwise hide them from lookup on a
  // Boolector solver. Their default throws NotImplementedException.
  using AbsSmtSolver::make_term;
  Term make_term(bool b) const override;
  Term make_term(int64_t i, const Sort & sort) const override;
  Term make_term(const std::string val,
                 const Sort & sort,
                 uint64_t base = 10) const override;
  Term make_term(const Term & val, const Sort & sort) const override;
  Term make_symbol(const std::string name, const Sort & sort) override;
  Term get_symbol(const std::string & name) override;
  Term make_param(const std::string name, const Sort & sort) override;
  /* build a new term */
  Term make_term(Op op, const Term & t) const override;
  Term make_term(Op op, const Term & t0, const Term & t1) const override;
  Term make_term(Op op,
                 const Term & t0,
                 const Term & t1,
                 const Term & t2) const override;
  Term make_term(Op op, const TermVec & terms) const override;
  void reset() override;
  void reset_assertions() override;
  Term substitute(const Term term,
                  const UnorderedTermMap & substitution_map) const override;
  // helper methods for making a term with a primitive op
  Term apply_prim_op(PrimOp op, Term t) const;
  Term apply_prim_op(PrimOp op, Term t0, Term t1) const;
  Term apply_prim_op(PrimOp op, Term t0, Term t1, Term t2) const;
  Term apply_prim_op(PrimOp op, TermVec terms) const;
  void dump_smt2(std::string filename) const override;

  // getters for solver-specific objects
  // for interacting with third-party Boolector-specific software

  Btor * get_btor() const { return btor; };

 protected:
  Btor * btor;

  std::unordered_map<std::string, Term> symbol_table;

  bool base_context_1 = false;
  ///< if set to true, do all solving at context 1 in the solver
  ///< this then supports reset_assertions by popping and re-pushing
  ///< the context. Without it, boolector does not support
  ///< reset_assertions yet
  ///< set this flag with set_opt("base-context-1", "true")
  size_t context_level = 0;  ///< tracks the current solving context level

  std::chrono::duration<double> time_limit{ 0 };   ///< zero means no limit
  std::chrono::steady_clock::time_point deadline;  ///< of the running query

  /** Termination callback: tells Boolector to stop once the deadline
   *  passes. Registered for the solver's whole life, because Boolector
   *  hands it to the SAT solver only when that is first created.
   *  @param solver the BoolectorSolver whose deadline to check
   */
  static int32_t reached_deadline(void * solver);

  /** Runs a query under the time limit, if one is set */
  Result solve();

  // helper functions
  template <class I>
  inline Result check_sat_assuming(I it, const I & end)
  {
    std::shared_ptr<BoolectorTerm> bt;
    while (it != end)
    {
      bt = std::static_pointer_cast<BoolectorTerm>(*it);
      assert(boolector_get_width(bt->btor, bt->node) == 1);
      boolector_assume(btor, bt->node);
      ++it;
    }

    return solve();
  }
};
}  // namespace smt
