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
   - Required: get_interpolant, get_sequence_interpolants and the hook
     do_set_opt. A backend usually computes only one of the first two
     natively, and implements the other with interpolant_from_sequence or
     sequence_from_interpolants; implementing both with them would recurse
     forever.
   - Handled here: set_opt takes incremental, which decides whether a query
     may reuse what it shares with the one before (on by default, and read
     from incremental_mode), and hands every other option to do_set_opt.
     An interpolating solver holds no assertions of the caller's, so
     reset_assertions discards what it keeps between queries instead, and
     the next query starts afresh; it never changes what a query answers.
     do_reset and do_reset_assertions are final: both forget the queries
     sequence_from_interpolants keeps for reuse, call forget_queries and
     then reset the regular solver, and do_reset also turns incremental
     back on and calls initialize. A backend overrides forget_queries if
     it keeps anything else between queries, and initialize if the regular
     solver needs setting up for interpolation, which its constructor then
     calls too.
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

  /** Takes incremental, and hands every other option to do_set_opt
   *  @throws IncorrectUsageException if incremental is neither true nor false
   */
  void set_opt(const std::string option, const std::string value) override;

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
  /** Takes an option other than incremental, which set_opt takes itself */
  virtual void do_set_opt(const std::string & option,
                          const std::string & value) = 0;

  // ------------------------- Handled here ---------------------------------
  /** Forgets the queries and resets the regular solver; see the contract */
  void do_reset_assertions() final;

  /** As do_reset_assertions, but resets the regular solver to its startup
   *  state, turns incremental back on and calls initialize
   */
  void do_reset() final;

  /** Drops what the interpolator keeps between queries, before the regular
   *  solver is reset; does nothing unless overridden
   */
  virtual void forget_queries();

  /** Sets up the regular solver for interpolation, again after reset
   *  returned it to its startup state; does nothing unless overridden. A
   *  constructor that needs it calls it itself, since the base class's
   *  constructor would only reach this one.
   */
  virtual void initialize();

  /** Computes the interpolant of A and B as the sequence interpolant of
   *  { A, B }, for a backend that computes sequences natively.
   */
  Result interpolant_from_sequence(const Term & A,
                                   const Term & B,
                                   Term & out_I) const;

  /** Computes a sequence interpolant with one get_interpolant call per
   *  split, for a backend that computes single interpolants natively. The
   *  first split interpolates the first formula against the conjunction of
   *  the rest; each later one interpolates the conjunction of the
   *  interpolant before it and the next formula instead of the whole
   *  prefix, which makes the interpolants a chain. Unless incremental_mode
   *  is off, a query that starts with all of the last unsat one keeps its
   *  interpolants and goes on from the last of them.
   */
  Result sequence_from_interpolants(const TermVec & formulae,
                                    TermVec & out_I) const;

  SmtSolver backend_solver;
  // false if each query starts afresh instead of reusing what it shares
  // with the one before
  bool incremental_mode = true;
  // for sequence_from_interpolants, the last sequence query and, if it was
  // unsat with every interpolant found, its interpolants, which stay valid
  // for a query that extends it
  mutable TermVec last_itp_query_formulae;
  mutable TermVec last_itp_query_interpolants;
};

}  // namespace smt
