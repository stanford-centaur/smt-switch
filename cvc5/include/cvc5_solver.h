/*********************                                                        */
/*! \file cvc5_solver.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief cvc5 implementation of AbsSmtSolver
**
**
**/

#pragma once

#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "cvc5/cvc5.h"
#include "cvc5_datatype.h"
#include "cvc5_sort.h"
#include "cvc5_term.h"
#include "interpolating_solver.h"
#include "smt.h"

namespace smt {
/**
   cvc5 Solver
 */
class Cvc5Solver : public AbsSmtSolver
{
 public:
  Cvc5Solver();
  Cvc5Solver(const Cvc5Solver &) = delete;
  Cvc5Solver & operator=(const Cvc5Solver &) = delete;
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
  Sort make_sort(SortKind sk, std::uint64_t size) const override;
  Sort make_sort(SortKind sk, const SortVec & sorts) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;
  Sort make_sort(const DatatypeDecl & d) const override;

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
  SortVec make_datatype_sorts(
      const std::vector<DatatypeDecl> & decls) const override;

  // Declaring make_term here hides the AbsSmtSolver template that takes
  // the children as separate arguments, so name it back in.
  using AbsSmtSolver::make_term;
  Term make_term(bool b) const override;
  Term make_term(std::int64_t i, const Sort & sort) const override;
  Term make_term(const std::string & s,
                 bool useEscSequences,
                 const Sort & sort) const override;
  Term make_term(const std::wstring & s, const Sort & sort) const override;
  Term make_term(const std::string val,
                 const Sort & sort,
                 std::uint64_t base = 10) const override;
  Term make_term(const Term & val, const Sort & sort) const override;
  Term make_symbol(const std::string name, const Sort & sort) override;
  Term get_symbol(const std::string & name) const override;
  Term make_param(const std::string name, const Sort & sort) const override;
  /* build a new term */
  Term make_term(Op op, const TermVec & terms) const override;
  Term substitute(const Term term,
                  const UnorderedTermMap & substitution_map) const override;

  // helpers
  ::cvc5::Op make_cvc5_op(Op op) const;

  // getters for solver-specific objects
  // for interacting with third-party cvc5-specific software

  /** @return the cvc5 solver; the handle keeps it and its term manager
   *  alive, so it stays usable after reset() or this solver's destruction,
   *  though this solver then stops using it
   */
  std::shared_ptr<cvc5::Solver> get_cvc5_solver();

  /** @return the term manager of this solver's terms and sorts; the handle
   *  keeps it alive, so it stays usable after reset() or this solver's
   *  destruction, though this solver then stops using it
   */
  std::shared_ptr<cvc5::TermManager> get_term_manager();

 protected:
  void do_push(std::uint64_t num) override;
  void do_pop(std::uint64_t num) override;
  void do_reset() override;
  void do_reset_assertions() override;

  // a cvc5 solver together with the term manager it uses
  struct Instance;

  std::shared_ptr<Instance> instance;

  std::unordered_map<std::string, Term> symbol_table;
};

// Interpolating Solver
class cvc5InterpolatingSolver : public AbsSmtInterpolator
{
 public:
  cvc5InterpolatingSolver();
  cvc5InterpolatingSolver(const cvc5InterpolatingSolver &) = delete;
  cvc5InterpolatingSolver & operator=(const cvc5InterpolatingSolver &) = delete;

  Result get_interpolant(const Term & A,
                         const Term & B,
                         Term & out_I) const override;
  Result get_sequence_interpolants(const TermVec & formulae,
                                   TermVec & out_I) const override;

 protected:
  void do_set_opt(const std::string & option,
                  const std::string & value) override;
  // sets the options interpolation needs, on construction and after reset()
  void initialize() override;

  // the regular solver that builds this solver's terms
  std::shared_ptr<Cvc5Solver> cvc5_solver;
};

}  // namespace smt
