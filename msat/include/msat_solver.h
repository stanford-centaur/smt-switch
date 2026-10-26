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
#include <utility>
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
   *  options can still be set until then. set_logic is refused, since the
   *  configuration for a logic would discard c's settings: make c with
   *  msat_create_default_config instead.
   */
  explicit MsatSolver(msat_config c);
  MsatSolver(const MsatSolver &) = delete;
  MsatSolver & operator=(const MsatSolver &) = delete;
  /** Sets an option. Refused once the environment exists: MathSAT makes
   *  every sort and term in it, so the first sort, term, assertion, check
   *  or push creates it, which fixes the configuration.
   */
  void set_opt(const std::string option, const std::string value) override;
  /** Sets the logic. Refused once the environment exists, as set_opt is. */
  void set_logic(const std::string logic_name) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  // Overriding check_sat_assuming hides the AbsSmtSolver template that
  // takes any range of Terms, so name it back in.
  using AbsSmtSolver::check_sat_assuming;
  Result check_sat_assuming(const TermVec & assumptions) override;
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

  // getters and setters for advanced use / testing
  size_t max_assump_clauses() const { return max_assump_clauses_; }

  void set_max_assump_clauses(size_t m) { max_assump_clauses_ = m; }

 protected:
  void do_push(uint64_t num) override;
  void do_pop(uint64_t num) override;
  void do_reset() override;
  void do_reset_assertions() override;

  bool valid_model = false;
  std::string logic;

  // for matching the generic check_sat_assuming interface which allows
  // arbitrary formulas rather than just (negated) boolean constants
  std::unordered_map<size_t, msat_term>
      assumption_map_;  ///< maps msat_term labels to assumptions
  std::vector<msat_term>
      base_assertions_;  ///< assertions at context level 0
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
    /** Takes ownership of c. */
    explicit EnvWrapper(msat_config c);
    EnvWrapper(const EnvWrapper &) = delete;
    EnvWrapper & operator=(const EnvWrapper &) = delete;

    /** Sets the logic, by making MathSAT's configuration for it. */
    void set_logic(const std::string & logic_name);
    /** Sets an option, or keeps it until there is a configuration. */
    void set_option(const std::string & name, const std::string & value);
    /** @return the environment, created on first use */
    const std::shared_ptr<msat_env> & get_env();
    /** @return whether the environment exists */
    bool is_initialized() const;
    /** Drops the environment and the configuration. */
    void reset();

   private:
    // empty until a configuration is made, and again once env owns it
    ConfigPtr cfg;
    // the options set while there is no configuration yet, in order
    std::vector<std::pair<std::string, std::string>> pending;
    // shared with every term and sort, so the environment lives until the
    // last of them is released, even past reset() or the solver's
    // destruction
    std::shared_ptr<msat_env> env;
  };

  // mutable, as const methods such as make_sort create the environment
  mutable EnvWrapper env_wrapper_;
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
  // sets what set_required_options does and the preferences for a
  // configuration of the solver's own, on construction without a
  // configuration and after reset()
  void initialize() override;
  // sets the options MathSAT cannot interpolate without, which a caller's
  // configuration needs too
  void set_required_options();

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
