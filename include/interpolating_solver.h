/*********************                                                        */
/*! \file interpolating_solver.h
** \verbatim
** Top contributors (to current version):
**   Áron Ricardo Perez-Lopez
** This file is part of the smt-switch project.
** Copyright (c) 2026 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Abstract interface for interpolating solvers.
**
**
**/

// IWYU pragma: private, include "smt.h"

#pragma once

#include <cstdint>
#include <string>
#include <vector>

#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"

namespace smt {

/**
   Abstract interpolating solver, to be implemented by each backend that
   supports interpolation. It answers interpolation queries only, and
   builds its terms and sorts with a regular solver of the same backend,
   which it holds and forwards those calls to.

   The contract:
   - Forbidden: push, pop, assert_formula, check_sat, check_sat_assuming
     and get_value throw IncorrectUsageException, and are final so that
     no interpolator can re-enable solving.
   - Required: get_interpolant and get_sequence_interpolants. A backend
     usually computes only one of them natively, and can implement the
     other with interpolant_from_sequence or sequence_from_interpolants.
   - Optional: set_opt, reset and reset_assertions throw
     NotImplementedException unless overridden.
   - Everything else is forwarded to the regular solver.
 */
class AbsSmtInterpolator : public AbsSmtSolver
{
 public:
  /** @param se the interpolator's SolverEnum
   *  @param backend_solver a fresh regular solver of the same backend, which
   *         builds the interpolator's terms and sorts
   */
  AbsSmtInterpolator(SolverEnum se, SmtSolver backend_solver);

  // ------------------------- Forbidden ------------------------------------
  void push(std::uint64_t num = 1) final;
  void pop(std::uint64_t num = 1) final;
  void assert_formula(const Term & t) final;
  Result check_sat() final;
  // Overriding check_sat_assuming hides the AbsSmtSolver template that
  // takes any range of Terms, so name it back in.
  using AbsSmtSolver::check_sat_assuming;
  Result check_sat_assuming(const TermVec & assumptions) final;
  Term get_value(const Term & t) const final;

  // ------------------------- Required -------------------------------------
  /* Compute a Craig interpolant given A and B such that A ^ B is unsat
   *   i.e. an I such that: A -> I  and  I ^ B is unsat
   *        and I only contains constants that are in both A and B
   * @param A the A term for a craig interpolant
   * @param B the B term for a craig interpolant
   * @param out_I the term to store the computed interpolant in
   * @return unsat    iff an interpolant was computed,
   *         sat      iff the query was satisfiable,
   *         unknown  iff interpolation failed
   *
   */
  virtual Result get_interpolant(const Term & A,
                                 const Term & B,
                                 Term & out_I) const = 0;

  /** Compute a sequence interpolants given formulae
   *  such that there is an interpolant between each adjacent formula in
   *  the vector formulae
   * @param formulae the formula terms to get sequence interpolants for
   * @param out_I the vector to store sequence interpolants in
   *              NOTE out_I can have null terms in it -- see below
   * @return unsat    iff the interpolants were computed,
   *         sat      iff the query was satisfiable,
   *         unknown  iff any step of the interpolation failed
   *                  in this case, out_I is still populated but any
   *                  failed steps have null terms
   *
   */
  virtual Result get_sequence_interpolants(const TermVec & formulae,
                                           TermVec & out_I) const = 0;

  // ------------------------- Optional -------------------------------------
  void set_opt(const std::string option, const std::string value) override;
  void reset() override;
  void reset_assertions() override;

  // ------------------------- Forwarded ------------------------------------
  void set_logic(const std::string logic) override;
  std::uint64_t get_context_level() const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) override;

  // Declaring make_sort here hides the AbsSmtSolver template that takes
  // the sorts as separate arguments, so name it back in.
  using AbsSmtSolver::make_sort;
  Sort make_sort(const std::string name, std::uint64_t arity) const override;
  Sort make_sort(const SortKind sk) const override;
  Sort make_sort(const SortKind sk, std::uint64_t size) const override;
  Sort make_sort(const SortKind sk, const SortVec & sorts) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;

  Term make_term(bool b) const override;
  Term make_term(std::int64_t i, const Sort & sort) const override;
  Term make_term(const std::string val,
                 const Sort & sort,
                 std::uint64_t base = 10) const override;
  Term make_term(const Term & val, const Sort & sort) const override;
  Term make_symbol(const std::string name, const Sort & sort) override;
  Term get_symbol(const std::string & name) override;
  Term make_param(const std::string name, const Sort & sort) override;
  Term make_term(const Op op, const Term & t) const override;
  Term make_term(const Op op, const Term & t0, const Term & t1) const override;
  Term make_term(const Op op,
                 const Term & t0,
                 const Term & t1,
                 const Term & t2) const override;
  Term make_term(const Op op, const TermVec & terms) const override;

  Term make_term(const std::string & s,
                 bool useEscSequences,
                 const Sort & sort) const override;
  Term make_term(const std::wstring & s, const Sort & sort) const override;

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

  Term substitute(const Term term,
                  const UnorderedTermMap & substitution_map) const override;
  TermVec substitute_terms(
      const TermVec & terms,
      const UnorderedTermMap & substitution_map) const override;
  void dump_smt2(std::string filename) const override;

 protected:
  /** Computes the interpolant of A and B as the sequence interpolant of
   *  { A, B }, for a backend that computes sequences natively.
   */
  Result interpolant_from_sequence(const Term & A,
                                   const Term & B,
                                   Term & out_I) const;

  /** Computes a sequence interpolant with one get_interpolant call per
   *  partition, for a backend that computes single interpolants natively.
   */
  Result sequence_from_interpolants(const TermVec & formulae,
                                    TermVec & out_I) const;

  SmtSolver backend_solver;
};

}  // namespace smt
