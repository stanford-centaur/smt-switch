/*********************                                                        */
/*! \file yices2_solver.h
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson, Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Yices2 implementation of AbsSmtSolver
**
**
**/

#pragma once

#include <gmp.h>
#include <memory>
#include <string>
#include <unordered_set>
#include <vector>

#include <yices.h>

#include "yices2_extensions.h"
#include "yices2_sort.h"
#include "yices2_term.h"

#include "exceptions.h"
#include "result.h"
#include "smt.h"
#include "sort.h"

namespace smt {
/**
   Yices2 Solver
 */
class Yices2Solver : public AbsSmtSolver
{
 public:
  Yices2Solver() : AbsSmtSolver(YICES2), pushes_after_unsat(0), context_level(0)
  {
    // Had to move yices_init to the Factory
    // yices_init();
    ctx = yices_new_context(NULL);
    config = yices_new_config();
  };
  Yices2Solver(const Yices2Solver &) = delete;
  Yices2Solver & operator=(const Yices2Solver &) = delete;
  ~Yices2Solver()
  {
    // need to destruct all stored terms in symbol_table
    symbol_table.clear();

    yices_free_config(config);
    yices_free_context(ctx);

    // TODO: Should probably find a good place to
    // call yices_exit.
    // yices_exit();
  };
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  Result check_sat_assuming_list(const TermList & assumptions) override;
  Result check_sat_assuming_set(const UnorderedTermSet & assumptions) override;
  void push(uint64_t num = 1) override;
  void pop(uint64_t num = 1) override;
  uint64_t get_context_level() const override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) override;
  Sort make_sort(const std::string name, uint64_t arity) const override;
  Sort make_sort(SortKind sk) const override;
  Sort make_sort(SortKind sk, uint64_t size) const override;
  Sort make_sort(SortKind sk, const Sort & sort1) const override;
  Sort make_sort(SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2) const override;
  Sort make_sort(SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2,
                 const Sort & sort3) const override;
  Sort make_sort(SortKind sk, const SortVec & sorts) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;
  Sort make_sort(const DatatypeDecl & d) const override;

  DatatypeDecl make_datatype_decl(const std::string & s) override;
  DatatypeConstructorDecl make_datatype_constructor_decl(
      const std::string s) override;
  void add_constructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const override;
  void add_selector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const override;
  void add_selector_self(DatatypeConstructorDecl & dt, const std::string & name) const override;
  Term get_constructor(const Sort & s, std::string name) const override;
  Term get_tester(const Sort & s, std::string name) const override;
  Term get_selector(const Sort & s, std::string con, std::string name) const override;

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
  void dump_smt2(std::string filename) const override;

 protected:
  mutable context_t * ctx;
  mutable ctx_config_t * config;

  // workaround for: https://github.com/makaimann/smt-switch/issues/218
  uint64_t pushes_after_unsat;  ///< how many pushes after trivial unsat context
                                ///< status

  uint64_t context_level;  ///< incremental solving context

  std::unordered_map<std::string, Term> symbol_table;
  ///< Keep track of declared symbols to avoid re-declaration
  ///< Note: Yices2 has a global symbol table, but we want it
  ///< associated with each solver instance. This is why we
  ///< can't rely on yices_get_term_by_name to see if name
  ///< has already been used.

  // helper function
  inline Result check_sat_assuming(const std::vector<term_t> & y_assumps)
  {
    smt_status_t res = yices_check_context_with_assumptions(
        ctx, NULL, y_assumps.size(), &y_assumps[0]);

    if (yices_error_code() != 0)
    {
      std::string msg(yices_error_string());
      throw InternalSolverException(msg.c_str());
    }

    if (res == STATUS_SAT)
    {
      return Result(SAT);
    }
    else if (res == STATUS_UNSAT)
    {
      return Result(UNSAT);
    }
    else
    {
      return Result(UNKNOWN);
    }
  }
};
}  // namespace smt

