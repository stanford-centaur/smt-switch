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

#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "msat_sort.h"
#include "msat_term.h"

#include "mathsat.h"

#include "exceptions.h"
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
  MsatSolver()
      : AbsSmtSolver(MSAT),
        cfg(msat_create_config()),
        env_uninitialized(true),
        logic(""),
        num_assump_clauses_(0),
        max_assump_clauses_(10000),
        last_query_assuming(true){};
  MsatSolver(msat_config c, msat_env e)
      : AbsSmtSolver(MSAT),
        cfg(c),
        env(e),
        env_uninitialized(false),
        valid_model(false),
        logic(""),
        num_assump_clauses_(0),
        max_assump_clauses_(10000)
    {
    };
  MsatSolver(const MsatSolver &) = delete;
  MsatSolver & operator=(const MsatSolver &) = delete;
  ~MsatSolver()
  {
    // Note: even with this, mathsat leaks
    // a program that just creates a msat_env leaks
    //  -- be careful, valgrind won't report leaks on statically compiled
    //  binaries
    if (!env_uninitialized)
    {
      msat_destroy_env(env);
    }
    msat_destroy_config(cfg);
  }
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string log) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  Result check_sat_assuming_list(const TermList & assumptions) override;
  Result check_sat_assuming_set(const UnorderedTermSet & assumptions) override;
  void push(uint64_t num = 1) override;
  void pop(uint64_t num = 1) override;
  uint64_t get_context_level() const override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) override;
  Sort make_sort(const std::string name, uint64_t arity) const override;
  Sort make_sort(SortKind sk) const override;
  Sort make_sort(SortKind sk, uint64_t size) const override;
  Sort make_sort(SortKind sk, const Sort & sort1) const override;
  Sort make_sort(SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2) const override;
  Sort make_sort(SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2,
                 const Sort & sort3) const override;
  Sort make_sort(SortKind sk, const SortVec & sorts) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;

  Sort make_sort(const DatatypeDecl & d) const override;

  DatatypeDecl make_datatype_decl(const std::string & s) override;
  DatatypeConstructorDecl make_datatype_constructor_decl(
      const std::string s) override;
  void add_constructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const override;
  void add_selector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const override;
  void add_selector_self(DatatypeConstructorDecl & dt, const std::string & name) const override;
  Term get_constructor(const Sort & s, std::string name) const override;
  Term get_tester(const Sort & s, std::string name) const override;
  Term get_selector(const Sort & s, std::string con, std::string name) const override;

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
  msat_env get_msat_env() const { return env; };

  // getters and setters for advanced use / testing
  size_t max_assump_clauses() const { return max_assump_clauses_; }

  void set_max_assump_clauses(size_t m) { max_assump_clauses_ = m; }

 protected:
  msat_config cfg;
  // marked mutable because want to stick with const interface for functions
  // but the environment cannot be created before setting options
  // it will be lazily created when first used (which might be in a const function)
  mutable msat_env env;
  mutable bool env_uninitialized;
  bool valid_model;
  std::string logic;

  // for matching the generic check_sat_assuming interface which allows
  // arbitrary formulas rather than just (negated) boolean constants
  std::unordered_map<size_t, msat_term>
      assumption_map_;  ///< maps msat_term labels to assumptions
  std::vector<msat_term>
      base_assertions_;  ///< assertions at context level 0
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
  void clear_assumption_clauses()
  {
    // can only reset at context 0, and only do so if
    // there's a "magic large number" of assumption clauses
    if (!msat_num_backtrack_points(env)
        && num_assump_clauses_ >= max_assump_clauses_)
    {
      num_assump_clauses_ = 0;
      msat_reset_env(env);
      // re-add actual assertions
      for (const auto & ba : base_assertions_)
      {
        msat_assert_formula(env, ba);
      }
    }
  }

  // initializes the env (if not already done)
  virtual void initialize_env() const
  {
    if (env_uninitialized)
    {
      env = msat_create_env(cfg);
      env_uninitialized = false;
    }
  }

  // helper function for creating labels for assumptions
  msat_term label(msat_term p) const;

  inline Result check_sat_assuming_msatvec(std::vector<msat_term> & m_assumps)
  {
    msat_term lbl;
    assumption_map_.clear();
    std::vector<msat_term> lbls;
    lbls.reserve(m_assumps.size());
    for (const auto & ma : m_assumps)
    {
      lbl = label(ma);
      // check that label is cached correctly
      assert(msat_term_id(lbl) == msat_term_id(label(ma)));
      msat_assert_formula(env, msat_make_or(env, msat_make_not(env, lbl), ma));
      num_assump_clauses_++;
      assumption_map_[msat_term_id(lbl)] = ma;
      lbls.push_back(lbl);
    }

    assert(lbls.size() == m_assumps.size());

    msat_result mres =
        msat_solve_with_assumptions(env, lbls.data(), lbls.size());

    if (mres == MSAT_SAT)
    {
      return Result(SAT);
    }
    else if (mres == MSAT_UNSAT)
    {
      return Result(UNSAT);
    }
    else
    {
      return Result(UNKNOWN);
    }
  }
};

// Interpolating Solver
class MsatInterpolatingSolver : public MsatSolver
{
 public:
  typedef MsatSolver super;
  MsatInterpolatingSolver() { solver_enum = MSAT_INTERPOLATOR; };
  MsatInterpolatingSolver(msat_config c, msat_env e)
  {
    cfg = c;
    env = e;
    solver_enum = MSAT_INTERPOLATOR;
  };
  MsatInterpolatingSolver(const MsatInterpolatingSolver &) = delete;
  MsatInterpolatingSolver & operator=(const MsatInterpolatingSolver &) = delete;
  ~MsatInterpolatingSolver() {}
  void set_opt(const std::string option, const std::string value) override;
  void push(uint64_t num = 1) override;
  void pop(uint64_t num = 1) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  Term get_value(const Term & t) const override;
  Result get_interpolant(const Term & A,
                         const Term & B,
                         Term & out_I) const override;
  Result get_sequence_interpolants(const TermVec & formulae,
                                   TermVec & out_I) const override;
  void reset() override;
  void reset_assertions() override;

 protected:
  virtual void initialize_env() const override
  {
    if (env_uninitialized)
    {
      msat_set_option(cfg, "theory.bv.eager", "false");
      msat_set_option(cfg, "theory.bv.bit_blast_mode", "0");
      msat_set_option(cfg, "interpolation", "true");
      msat_set_option(cfg, "incremental", "true");
      // TODO: decide if we should add this
      // msat_set_option(cfg, "theory.eq_propagation", "false");
      env = msat_create_env(cfg);
      env_uninitialized = false;
    }
  }

  // assertions from the last interpolation query, indexed by the context level
  // (although one can get assertions using `msat_get_asserted_formulas`,
  // the method does not guarantee that the assertions are in the correct order)
  mutable TermVec last_itp_query_assertions_;
  // interpolation group for each assertion level
  mutable std::vector<int> itp_grps_;
};

}  // namespace smt
