/*********************                                                        */
/*! \file msat_solver.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief MathSAT implementation of AbsSmtSolver
**
**
**/

#pragma once

#include <cassert>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "exceptions.h"
#include "interpolating_solver.h"
#include "mathsat.h"
#include "msat_sort.h"
#include "msat_term.h"
#include "ops.h"
#include "result.h"
#include "smt.h"
#include "sort.h"
#include "term.h"

namespace smt {
/**
   Msat Solver
 */
class MsatSolver : public AbsSmtSolver
{
 public:
  MsatSolver();
  /** Creates a solver from a configuration and takes ownership of it: the
   *  solver destroys c. The environment is created from c on first use, so
   *  options can still be set until then.
   */
  explicit MsatSolver(msat_config c);
  /** Deprecated: create the environment from the configuration with
   *  MsatSolver(msat_config) instead. Takes ownership of both c and e, and
   *  uses e as the environment, so no options can be set.
   */
  [[deprecated("use MsatSolver(msat_config), which creates the env")]]
  MsatSolver(msat_config c, msat_env e);
  MsatSolver(const MsatSolver &) = delete;
  MsatSolver & operator=(const MsatSolver &) = delete;
  ~MsatSolver();
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string log) override;
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
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;

  // AbsSmtSolver's string-value overloads are not declared here, and a
  // declaration of the name would otherwise hide them from lookup on a
  // MathSAT solver. Their default throws NotImplementedException.
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

  void dump_smt2(std::string filename) const override;

  // getters for solver-specific objects
  // for interacting with third-party MathSAT-specific software
  // creates the environment if it does not exist yet
  msat_env get_msat_env() const;

  // getters and setters for advanced use / testing
  size_t max_assump_clauses() const { return max_assump_clauses_; }

  void set_max_assump_clauses(size_t m) { max_assump_clauses_ = m; }

 protected:
  msat_config cfg;
  // marked mutable because want to stick with const interface for functions
  // but the environment cannot be created before setting options
  // it will be lazily created when first used (which might be in a const
  // function)
  mutable msat_env env;
  mutable bool env_uninitialized;
  bool valid_model;
  std::string logic;

  // for matching the generic check_sat_assuming interface which allows
  // arbitrary formulas rather than just (negated) boolean constants
  std::unordered_map<size_t, msat_term>
      assumption_map_;  ///< maps msat_term labels to assumptions
  std::vector<msat_term>
      base_assertions_;        ///< assertions at context level 0
                               ///< to be re-added after resetting to clear old
                               ///< clauses added for assumptions
  size_t num_assump_clauses_;  ///< counts how many assumption clauses are added
  size_t max_assump_clauses_;  ///< number of assumption clauses before clearing
                               ///< them
  bool last_query_assuming;    ///< set to true if last query was
                               ///< check-sat-assuming (as opposed to
                               ///< just check-sat).
                               ///< This boolean is used to respect the
                               ///< get_unsat_assumptions interface (will
                               ///< complain if not called after
                               ///< check-sat-assuming).

  // clears assumption clauses
  // needed to simulate the same check_sat_assuming interface as other solvers
  // called before a check-sat or check-sat-assuming call
  void clear_assumption_clauses();

  // initializes the env (if not already done)
  virtual void initialize_env() const;

  // helper function for creating labels for assumptions
  msat_term label(msat_term p) const;

  Result check_sat_assuming_msatvec(std::vector<msat_term> & m_assumps);
};

// Interpolating Solver
class MsatInterpolatingSolver : public AbsSmtInterpolator
{
 public:
  MsatInterpolatingSolver();
  /** Creates an interpolating solver from a configuration and takes
   *  ownership of it: the solver destroys c. It sets the two options
   *  MathSAT cannot interpolate without, interpolation=true and
   *  theory.bv.eager=false, and the environment is created from c on
   *  first use. Every other option on c is left as given.
   */
  explicit MsatInterpolatingSolver(msat_config c);
  /** Deprecated: use MsatInterpolatingSolver(msat_config). Takes ownership
   *  of both c and e, like MsatSolver(msat_config, msat_env), but destroys
   *  e at once: interpolation has to be enabled on the configuration before
   *  the environment is created, so the solver creates its own.
   */
  [[deprecated("use MsatInterpolatingSolver(msat_config); e is destroyed")]]
  MsatInterpolatingSolver(msat_config c, msat_env e);
  MsatInterpolatingSolver(const MsatInterpolatingSolver &) = delete;
  MsatInterpolatingSolver & operator=(const MsatInterpolatingSolver &) = delete;
  ~MsatInterpolatingSolver() {}
  void set_opt(const std::string option, const std::string value) override;
  Result get_interpolant(const Term & A,
                         const Term & B,
                         Term & out_I) const override;
  Result get_sequence_interpolants(const TermVec & formulae,
                                   TermVec & out_I) const override;
  void reset() override;
  void reset_assertions() override;

 protected:
  // the regular solver that builds this solver's terms
  std::shared_ptr<MsatSolver> msat_solver_;

  // assertions from the last interpolation query, indexed by the context level
  // (although one can get assertions using `msat_get_asserted_formulas`,
  // the method does not guarantee that the assertions are in the correct order)
  mutable TermVec last_itp_query_assertions_;
  // interpolation group for each assertion level
  mutable std::vector<int> itp_grps_;
};

}  // namespace smt
