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
  ~Cvc5Solver() = default;
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  // Overriding check_sat_assuming hides the AbsSmtSolver template that
  // takes any range of Terms, so name it back in.
  using AbsSmtSolver::check_sat_assuming;
  Result check_sat_assuming(const TermVec & assumptions) override;
  void push(std::uint64_t num = 1) override;
  void pop(std::uint64_t num = 1) override;
  uint64_t get_context_level() const override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) override;
  // Declaring make_sort here at all would hide AbsSmtSolver's own overloads
  // from lookup on this type, so name them back in.
  using AbsSmtSolver::make_sort;
  Sort make_sort(const std::string name, uint64_t arity) const override;
  Sort make_sort(SortKind sk) const override;
  Sort make_sort(SortKind sk, std::uint64_t size) const override;
  Sort make_sort(SortKind sk, const SortVec & sorts) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;
  Sort make_sort(const DatatypeDecl & d) const override;

  DatatypeDecl make_datatype_decl(const std::string & s) override;
  DatatypeConstructorDecl make_datatype_constructor_decl(
      const std::string s) override;
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

  // helpers
  ::cvc5::Op make_cvc5_op(Op op) const;

  // getters for solver-specific objects
  // for interacting with third-party cvc5-specific software
  ::cvc5::Solver & get_cvc5_solver();

 protected:
  std::unique_ptr<::cvc5::TermManager> term_manager;
  ::cvc5::Solver solver;

  std::unordered_map<std::string, Term> symbol_table;

  std::uint64_t context_level = 0;

  // helper function
  Result check_sat_assuming(const std::vector<cvc5::Term> & cvc5assumps);
};

// Interpolating Solver
class cvc5InterpolatingSolver : public AbsSmtInterpolator
{
 public:
  cvc5InterpolatingSolver();
  cvc5InterpolatingSolver(const cvc5InterpolatingSolver &) = delete;
  cvc5InterpolatingSolver & operator=(const cvc5InterpolatingSolver &) = delete;
  ~cvc5InterpolatingSolver() {}

  void set_opt(const std::string option, const std::string value) override;
  Result get_interpolant(const Term & A,
                         const Term & B,
                         Term & out_I) const override;
  Result get_sequence_interpolants(const TermVec & formulae,
                                   TermVec & out_I) const override;
  void reset_assertions() override;

 protected:
  // the regular solver that builds this solver's terms
  std::shared_ptr<Cvc5Solver> cvc5_solver;
};

}  // namespace smt
