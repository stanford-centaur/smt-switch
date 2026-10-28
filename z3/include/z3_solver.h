/*********************                                                        */
/*! \file z3_solver.h
** \verbatim
** Top contributors (to current version):
**   Lindsey Stuntz
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Z3 implementation of AbsSmtSolver
**
**
**/

#pragma once

#include <z3++.h>

#include <cstdint>
#include <memory>
#include <string>
#include <unordered_set>
#include <vector>

#include "exceptions.h"
#include "result.h"
#include "smt.h"
#include "sort.h"
#include "z3_datatype.h"
#include "z3_sort.h"
#include "z3_term.h"

namespace smt {
/**
   Z3 Solver
 */
class Z3Solver : public AbsSmtSolver
{
 public:
  Z3Solver();
  Z3Solver(const Z3Solver &) = delete;
  Z3Solver & operator=(const Z3Solver &) = delete;
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  // Overriding check_sat_assuming hides the AbsSmtSolver template that
  // takes any range of Terms, so name it back in.
  using AbsSmtSolver::check_sat_assuming;
  Result check_sat_assuming(const TermVec & assumptions) override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) const override;
  // Declaring make_sort here at all would hide AbsSmtSolver's own overloads
  // from lookup on this type, so name them back in.
  using AbsSmtSolver::make_sort;
  Sort make_sort(const std::string name, uint64_t arity) const override;
  Sort make_sort(SortKind sk) const override;
  Sort make_sort(SortKind sk, uint64_t size) const override;
  Sort make_sort(SortKind sk, const SortVec & sorts) const override;
  Sort make_sort(const DatatypeDecl & d) const override;
  SortVec make_datatype_sorts(
      const std::vector<DatatypeDecl> & decls) const override;

  DatatypeDecl make_datatype_decl(const std::string & s) const override;
  DatatypeConstructorDecl make_datatype_constructor_decl(
      const std::string s) const override;
  void add_constructor(DatatypeDecl & dt,
                       const DatatypeConstructorDecl & con) const override;
  void add_selector(DatatypeConstructorDecl & dt,
                    const std::string & name,
                    const Sort & s) const override;
  void add_selector_self(DatatypeConstructorDecl & dt,
                         const std::string & name) const override;
  Term get_constructor(const Sort & s, std::string name) const override;
  Term get_tester(const Sort & s, std::string name) const override;
  Term get_selector(const Sort & s,
                    std::string con,
                    std::string name) const override;

  // AbsSmtSolver's string-value overloads are not declared here, and a
  // declaration of the name would otherwise hide them from lookup on a
  // Z3 solver. Their default throws NotImplementedException.
  using AbsSmtSolver::make_term;

  Term make_term(bool b) const override;
  Term make_term(int64_t i, const Sort & sort) const override;
  Term make_term(const std::string val,
                 const Sort & sort,
                 uint64_t base = 10) const override;
  Term make_term(const Term & val, const Sort & sort) const override;
  Term make_symbol(const std::string name, const Sort & sort) override;
  Term get_symbol(const std::string & name) const override;
  Term make_param(const std::string name, const Sort & sort) const override;
  /* build a new term */
  Term make_term(Op op, const TermVec & terms) const override;
  Term substitute(const Term term,
                  const UnorderedTermMap & substitution_map) const override;

  // getters for solver-specific objects (EXPERTS ONLY)

  /** @return the context of this solver's terms and sorts; the handle keeps
   *  it alive, so it stays usable after this solver's destruction
   */
  std::shared_ptr<z3::context> get_z3_context();

  /** @return the Z3 solver, created on first use; the handle keeps it and
   *  its context alive, so it stays usable after reset() or this solver's
   *  destruction, though this solver then stops using it
   */
  std::shared_ptr<z3::solver> get_z3_solver();

 protected:
  void do_push(uint64_t num) override;
  void do_pop(uint64_t num) override;
  void do_reset() override;
  void do_reset_assertions() override;

  // shared with every term and sort, so the context lives until the last of
  // them is released, even past this solver's destruction
  std::shared_ptr<z3::context> ctx;
  // a Z3 solver together with the context it lives in
  struct Instance;

  // made for its logic by set_logic, or else as Z3's default by the first
  // assertion, check or push
  std::shared_ptr<Instance> instance;
  // every option set so far, for slv
  z3::params solver_params;
  std::unordered_map<std::string, Term> symbol_table;
  ///< keep track of declared symbols to avoid
  ///< redeclaring

  bool last_query_assuming = false;  ///< used to determine if last query was
                                     ///< check_sat_assuming (vs just check_sat)

  // helper function
  void add_constructor(z3::sort,
                       z3::constructors *,
                       const DatatypeConstructorDecl &) const;
};
}  // namespace smt
