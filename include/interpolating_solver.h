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
   - Forbidden: push, pop, assert_formula, check_sat, check_sat_assuming,
     get_value, get_array_values and get_unsat_assumptions throw
     IncorrectUsageException, and are final so that no interpolator can
     re-enable solving; for push and pop, it is their hooks do_push and
     do_pop that throw and are final. dump_smt2 throws it and is final as
     well, since an interpolator holds no assertions to dump.
     get_context_level is final too, and returns 0, since no context can
     be pushed.
   - Required: get_interpolant, get_sequence_interpolants, set_opt, and
     the hooks do_reset_assertions and do_reset. A backend can implement
     get_interpolant with interpolant_from_sequence.
     An interpolating solver holds no assertions of the caller's, so its
     reset_assertions discards what it keeps between queries instead: a
     backend may reuse the formulas a query shares with the one before,
     and after reset_assertions the next query starts afresh. It never
     changes what a query answers. A backend that keeps nothing between
     queries implements it as doing nothing, and one that reuses formulas
     also takes incremental set to false, to start every query afresh.
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
  void assert_formula(const Term & t) final;
  Result check_sat() final;
  // Overriding check_sat_assuming hides the AbsSmtSolver template that
  // takes any range of Terms, so name it back in.
  using AbsSmtSolver::check_sat_assuming;
  Result check_sat_assuming(const TermVec & assumptions) final;
  Term get_value(const Term & t) const final;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const final;
  void get_unsat_assumptions(UnorderedTermSet & out) final;
  void dump_smt2(std::string filename) const final;
  std::uint64_t get_context_level() const final;

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

  /** Compute a sequence interpolant given formulae F_0, ..., F_n whose
   *  conjunction is unsat, i.e. I_0, ..., I_{n-1} such that:
   *    F_0 -> I_0,
   *    I_{i-1} ^ F_i -> I_i  for each 0 < i < n, and
   *    I_{n-1} ^ F_n is unsat,
   *  where each I_i only contains constants that are in both F_0, ..., F_i
   *  and F_{i+1}, ..., F_n. So each I_i is also a Craig interpolant between
   *  the conjunction of F_0, ..., F_i and that of F_{i+1}, ..., F_n.
   * @param formulae the formula terms to get sequence interpolants for
   * @param out_I the vector to store sequence interpolants in
   *              NOTE out_I can have null terms in it -- see below
   * @return unsat    iff the interpolants were computed,
   *         sat      iff the query was satisfiable,
   *         unknown  iff any step of the interpolation failed
   *                  in this case, out_I is still populated but any
   *                  failed steps, and possibly the steps after them,
   *                  have null terms
   *
   */
  virtual Result get_sequence_interpolants(const TermVec & formulae,
                                           TermVec & out_I) const = 0;

  void set_opt(const std::string option, const std::string value) override = 0;

  // ------------------------- Forwarded ------------------------------------
  void set_logic(const std::string logic) override;

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

 protected:
  // ------------------------- Forbidden ------------------------------------
  void do_push(std::uint64_t num) final;
  void do_pop(std::uint64_t num) final;

  // ------------------------- Required -------------------------------------
  /** Discard what the solver keeps between queries, so that the next one
   *  starts afresh; see the contract above.
   */
  void do_reset_assertions() override = 0;

  void do_reset() override = 0;

  /** Computes the interpolant of A and B as the sequence interpolant of
   *  { A, B }, for a backend that computes sequences natively.
   */
  Result interpolant_from_sequence(const Term & A,
                                   const Term & B,
                                   Term & out_I) const;

  SmtSolver backend_solver;
};

}  // namespace smt
