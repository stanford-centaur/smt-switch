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

#include <mathsat.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "interpolating_solver.h"
#include "msat_env.h"
#include "msat_sort.h"
#include "msat_term.h"
#include "smt_defs.h"
#include "solver.h"
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
  MsatSolver(const MsatSolver &) = delete;
  MsatSolver & operator=(const MsatSolver &) = delete;
  /** Sets an option. Refused once the environment exists: MathSAT makes
   *  every sort and term in it, so the first sort, term, assertion, check
   *  or push creates it, which fixes the configuration.
   */
  void set_opt(const std::string option, const std::string value) override;
  /** Sets the logic. Once the environment exists, as for set_opt, or once
   *  a logic was set, only that same logic is accepted, and it changes
   *  nothing. With no logic set, the environment is made from MathSAT's
   *  plain configuration, which has every theory and so counts as ALL.
   */
  void set_logic(const std::string logic_name) override;
  Result check_sat() override;
  uint64_t get_context_level() const override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) const override;

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
  Term get_symbol(const std::string & name) const override;
  Term make_param(const std::string name, const Sort & sort) const override;
  /* build a new term */
  Term make_term(Op op, const TermVec & terms) const override;
  Term substitute(const Term term,
                  const UnorderedTermMap & substitution_map) const override;

  void dump_smt2(std::string filename) const override;

  // getters for solver-specific objects
  // for interacting with third-party MathSAT-specific software

  /** @return the environment, created on first use; the handle keeps it
   *  alive, so it stays usable after reset() or this solver's destruction,
   *  though this solver then stops using it
   */
  std::shared_ptr<msat_env> get_msat_env();

  // true once the environment exists, which fixes the configuration
  bool is_initialized() const;

  // Getters and setters for advanced use / testing
  size_t max_assump_clauses() const;

  void set_max_assump_clauses(size_t m);

 protected:
  void do_assert(const Term & t) override;
  Result do_check_sat_assuming(const TermVec & assumptions) override;
  void do_push(uint64_t num) override;
  void do_pop(uint64_t num) override;
  void do_reset() override;
  void do_reset_assertions() override;

  bool valid_model = false;

  // for matching the generic check_sat_assuming interface which allows
  // arbitrary formulas rather than just (negated) boolean constants
  std::unordered_map<size_t, msat_term>
      assumption_map_ = {};  ///< maps msat_term labels to assumptions
  std::vector<msat_term>
      base_assertions_ = {};  ///< assertions at context level 0
                              ///< to be re-added after resetting to clear old
                              ///< clauses added for assumptions
  size_t num_assump_clauses_ = 0;      ///< counts how many assumption clauses
                                       ///< are added
  size_t max_assump_clauses_ = 10000;  ///< number of assumption clauses before
                                       ///< clearing them
  bool last_query_assuming = true;     ///< set to true if last query was
                                       ///< check-sat-assuming (as opposed to
                                       ///< just check-sat).
                                       ///< This boolean is used to respect the
                                       ///< get_unsat_assumptions interface
                                       ///< (will complain if not called after
                                       ///< check-sat-assuming).

  // clears assumption clauses
  // needed to simulate the same check_sat_assuming interface as other solvers
  // called before a check-sat or check-sat-assuming call
  void clear_assumption_clauses();

  // helper function for creating labels for assumptions
  msat_term label(msat_term p) const;

  friend class MsatInterpolatingSolver;

 private:
  /** Destroys the configuration whose handle is repr. */
  struct ConfigDeleter
  {
    void operator()(void * repr) const;
  };
  using ConfigPtr = std::unique_ptr<void, ConfigDeleter>;
  /** @return the MathSAT handle of the configuration cfg holds */
  static msat_config as_msat_config(const ConfigPtr & cfg);

  /** Casts a term to pass to MathSAT, which would take another
   *  environment's term as one of its own
   *  @param t the term a caller passed to this solver
   *  @return t as a MsatTerm
   *  @throws IncorrectUsageException if t was made by another solver, or
   *          by this one before a reset()
   */
  std::shared_ptr<MsatTerm> get_msat_term(const Term & t) const;
  /** Casts a sort to pass to MathSAT, which would take another
   *  environment's type as one of its own
   *  @param s the sort a caller passed to this solver
   *  @return s as a MsatSort
   *  @throws IncorrectUsageException if s was made by another solver, or
   *          by this one before a reset()
   */
  std::shared_ptr<MsatSort> get_msat_sort(const Sort & s) const;

  /** The configuration and the environment made from it. Only get_env()
   *  hands out the environment, so no method can use one that does not
   *  exist yet. No configuration is made before one is needed, as MathSAT
   *  takes a logic only when it makes one.
   */
  class EnvWrapper
  {
   public:
    /** Starts with no configuration. */
    EnvWrapper() = default;
    EnvWrapper(const EnvWrapper &) = delete;
    EnvWrapper & operator=(const EnvWrapper &) = delete;

    /** Sets the logic, by making MathSAT's configuration for it. Once
     *  there is a configuration, only its own logic is accepted.
     */
    void set_logic(const std::string & logic_name);
    /** Sets an option, or keeps it until there is a configuration. */
    void set_option(const std::string & name, const std::string & value);
    /** @return the environment, created on first use */
    const std::shared_ptr<MsatEnv> & get_env();
    /** @return whether the environment exists */
    bool is_initialized() const;
    /** @return whether e is the environment, without creating it */
    bool owns(const std::shared_ptr<MsatEnv> & e) const;
    /** Drops the environment and the configuration. */
    void reset();
    /** @return the logic the configuration was made for, or an empty
     *  string before there is one
     */
    const std::string & get_logic() const;

   private:
    // empty until a configuration is made, and again once env owns it
    ConfigPtr cfg = nullptr;
    // the options set while there is no configuration yet, in order
    std::vector<std::pair<std::string, std::string>> pending = {};
    // the logic the configuration was made for, held by cfg or by env, ALL
    // for the plain configuration, and empty while there is none
    std::string logic = "";
    // shared with every term and sort, so the environment lives until the
    // last of them is released, even past reset() or the solver's
    // destruction
    std::shared_ptr<MsatEnv> env = nullptr;
  };

  // mutable, as const methods such as make_sort create the environment
  mutable EnvWrapper env_wrapper_ = {};
};

// Interpolating Solver
class MsatInterpolatingSolver : public AbsSmtInterpolator
{
 public:
  MsatInterpolatingSolver();
  MsatInterpolatingSolver(const MsatInterpolatingSolver &) = delete;
  MsatInterpolatingSolver & operator=(const MsatInterpolatingSolver &) = delete;
  Result get_interpolant(const Term & A,
                         const Term & B,
                         Term & out_I) const override;
  Result get_sequence_interpolants(const TermVec & formulae,
                                   TermVec & out_I) const override;

 protected:
  void do_set_opt(const std::string & option,
                  const std::string & value) override;
  void forget_queries() override;
  // sets the options MathSAT cannot interpolate without and the solver's
  // preferences, on construction and after reset()
  void initialize() override;

  // the regular solver that builds this solver's terms
  std::shared_ptr<MsatSolver> msat_solver_;

  // assertions from the last interpolation query, indexed by the context level
  // (although one can get assertions using `msat_get_asserted_formulas`,
  // the method does not guarantee that the assertions are in the correct order)
  mutable TermVec last_itp_query_assertions_ = {};
  // interpolation group for each assertion level
  mutable std::vector<int> itp_grps_ = {};
};

}  // namespace smt
