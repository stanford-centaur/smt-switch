/*!
 * \file interpolator.h
 * \brief Abstract interface for interpolating solvers
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_INTERPOLATOR_H
#define SMT_SWITCH_INTERPOLATOR_H

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/term_builder.h"

namespace smt {

using TermsPairVec = std::vector<std::pair<Term, Term>>;

/**
   Abstract interpolator, to be implemented by each backend that supports
   interpolation. It answers interpolation queries, and builds its terms
   and sorts with a regular solver of the same backend, which it holds and
   forwards those calls to.

   The contract:
   - Required: the hooks compute_interpolant, compute_seq_interpolants
     and do_set_opt. A backend usually computes only one of the first two
     natively, and implements the other with interpolant_from_sequence or
     sequence_from_interpolants; implementing both with them would recurse
     forever.
   - Handled here: set_opt takes incremental, which decides whether a query
     may reuse what it shares with the one before (on by default, and read
     from incremental_mode), and hands every other option to do_set_opt.
     An interpolator holds no assertions of the caller's, so
     reset_assertions discards what it keeps between queries instead, and
     the next query starts afresh; it never changes what a query answers.
     reset and reset_assertions both forget the queries
     sequence_from_interpolants keeps for reuse, call forget_queries and
     then reset the regular solver through reset_backend and
     reset_backend_assertions, and reset also turns incremental back on and
     calls initialize. A backend overrides forget_queries if it keeps
     anything else between queries, and initialize if the regular solver
     needs setting up for interpolation, which its constructor then calls
     too.
   - Optional: refute_model, one round of a backend that interpolates by
     refuting models of B.
   - Everything else is forwarded to the regular solver.
 */
class AbsSmtInterpolator : public AbsSmtTermBuilder
{
 public:
  /** @param itp_kind the interpolator's kind
   *  @param backend a fresh regular solver of the same backend, which
   *         builds the interpolator's terms and sorts
   */
  AbsSmtInterpolator(InterpolatorKind itp_kind, SmtSolver backend);

  /** @return the interpolator's kind */
  InterpolatorKind get_kind() const;

  /** @return an enum identifying the interpolator */
  [[deprecated("use get_kind")]] SolverEnum get_solver_enum() const;

  // ------------------------- Interpolation --------------------------------
  /* Compute a Craig interpolant given A and B such that A ^ B is unsat
   *   i.e. an I such that: A -> I  and  I ^ B is unsat
   *        and I only contains constants that are in both A and B
   * @param A the A term for a craig interpolant
   * @param B the B term for a craig interpolant
   * @param out_I the term to store the computed interpolant in
   * @return unsat    iff an interpolant was computed,
   *         sat      iff the query was satisfiable,
   *         unknown  iff interpolation failed
   * @throws IncorrectUsageException if A or B is not boolean
   */
  Result get_interpolant(const Term & A, const Term & B, Term & out_I) const;

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
   * @throws IncorrectUsageException if there are fewer than two formulae,
   *         one is not boolean, or out_I is not empty
   */
  Result get_sequence_interpolants(const TermVec & formulae,
                                   TermVec & out_I) const;

  /** Takes incremental, and hands every other option to do_set_opt
   *  SMTLIB: (set-option :<option> <value>)
   *  @throws IncorrectUsageException if incremental is neither true nor false
   */
  virtual void set_opt(const std::string option, const std::string value);

  /** Sets the logic of the regular solver
   *  SMTLIB: (set-logic <logic>)
   */
  virtual void set_logic(const std::string logic);

  /** Forgets the queries and drops the regular solver's assertions; see the
   *  contract
   *  SMTLIB: (reset-assertions)
   */
  void reset_assertions();

  /** As reset_assertions, but returns the regular solver to its startup
   *  state, which destroys all created terms and sorts, turns incremental
   *  back on and calls initialize
   *  SMTLIB: (reset)
   */
  void reset();

  // ------------------------- Forwarded ------------------------------------
  // Declaring make_sort here hides the AbsSmtTermBuilder template that takes
  // the sorts as separate arguments, so name it back in.
  using AbsSmtTermBuilder::make_sort;
  Sort make_sort(const std::string name, std::uint64_t arity) const override;
  Sort make_sort(const SortKind sk) const override;
  Sort make_sort(const SortKind sk, std::uint64_t size) const override;
  Sort make_sort(const SortKind sk, const SortVec & sorts) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;

  // Declaring make_term here hides the AbsSmtTermBuilder template that takes
  // the children as separate arguments, so name it back in.
  using AbsSmtTermBuilder::make_term;
  Term make_term(bool b) const override;
  Term make_term(std::int64_t i, const Sort & sort) const override;
  Term make_term(const std::string val,
                 const Sort & sort,
                 std::uint64_t base = 10) const override;
  Term make_term(const Term & val, const Sort & sort) const override;
  Term make_symbol(const std::string name, const Sort & sort) override;
  Term get_symbol(const std::string & name) const override;
  Term make_param(const std::string name, const Sort & sort) const override;
  Term make_term(const Op op, const TermVec & terms) const override;

  Term make_term(const std::string & s,
                 bool useEscSequences,
                 const Sort & sort) const override;
  Term make_term(const std::wstring & s, const Sort & sort) const override;

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

  Term substitute(const Term term,
                  const UnorderedTermMap & substitution_map) const override;
  TermVec substitute_terms(
      const TermVec & terms,
      const UnorderedTermMap & substitution_map) const override;

 protected:
  // ------------------------- Required -------------------------------------
  /** Computes an interpolant of boolean A and B; see get_interpolant */
  virtual Result compute_interpolant(const Term & A,
                                     const Term & B,
                                     Term & out_I) const = 0;

  /** Computes a sequence interpolant of at least two boolean formulae into
   *  an empty out_I; see get_sequence_interpolants
   */
  virtual Result compute_seq_interpolants(const TermVec & formulae,
                                          TermVec & out_I) const = 0;

  /** Takes an option other than incremental, which set_opt takes itself */
  virtual void do_set_opt(const std::string & option,
                          const std::string & value) = 0;

  // ------------------------- Handled here ---------------------------------
  /** Drops the regular solver's assertions; see reset_assertions */
  virtual void reset_backend_assertions();

  /** Returns the regular solver to its startup state; see reset */
  virtual void reset_backend();

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

  /** One round of interpolating A and B by refuting models of B: checks B
   *  with the model interpolants of the rounds before, and if it has a
   *  model, checks A with the shared symbols fixed to their values in it.
   *  Once B has no model left, the conjunction of the model interpolants
   *  is an interpolant. Throws NotImplementedException unless overridden.
   *  @param A the A term, which must be Boolean
   *  @param B the B term, which must be Boolean
   *  @param solver_a the solver the query checks A with, null before its
   *         first round, which makes it and asserts A
   *  @param solver_b the same for B, to which each model interpolant is
   *         added
   *  @param model an empty vector, which is set, if B has a model, to each
   *         symbol A and B share paired with its value in that model; a
   *         value that has no term, such as an algebraic number, is null
   *  @param model_interpolant set, if A refutes the model, to a formula
   *         that A implies and the model falsifies
   *  @return B's answer if it has no model, and otherwise A's under it,
   *          which is unsat if A refutes the model
   */
  virtual Result refute_model(const Term & A,
                              const Term & B,
                              SmtSolver & solver_a,
                              SmtSolver & solver_b,
                              TermsPairVec & model,
                              Term & model_interpolant) const;

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
  mutable TermVec last_itp_query_formulae = {};
  mutable TermVec last_itp_query_interpolants = {};

  // to run the rounds of refute_model on the interpolator it wraps
  friend class PrintingInterpolator;

 private:
  InterpolatorKind interpolator_kind;
};

}  // namespace smt

#endif  // SMT_SWITCH_INTERPOLATOR_H
