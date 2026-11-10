/*********************                                                        */
/*! \file yices2_solver.h
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson, Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Yices2 implementation of AbsSmtSolver
**
**
**/

#pragma once

#include <gmp.h>  // IWYU pragma: keep (required by yices.h)
#include <yices.h>
#include <yices_types.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"
#include "yices2_instance_ref.h"

// Yices2 2.7.0 renamed the smt_status_t enumerators to YICES_STATUS_*, and
// aliases only STATUS_INTERRUPTED back to its old spelling. Give the two
// names used here the same treatment, so this backend keeps building
// against 2.6. Drop this once 2.6 is no longer supported.
#if __YICES_VERSION == 2 && __YICES_VERSION_MAJOR < 7
#define YICES_STATUS_SAT STATUS_SAT
#define YICES_STATUS_UNSAT STATUS_UNSAT
#endif

namespace smt {

/**
   Yices2 Solver
 */
class Yices2Solver : public AbsSmtSolver
{
 public:
  Yices2Solver();
  Yices2Solver(const Yices2Solver &) = delete;
  Yices2Solver & operator=(const Yices2Solver &) = delete;
  ~Yices2Solver() override;
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  Result check_sat() override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) const override;

  // The datatype methods are left to AbsSmtSolver, whose defaults throw.
  // Declaring make_sort here at all would hide AbsSmtSolver's own overloads
  // from lookup on this type, so name them back in.
  using AbsSmtSolver::make_sort;
  Sort make_sort(const std::string name, uint64_t arity) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;
  Sort make_sort(SortKind sk) const override;
  Sort make_sort(SortKind sk, uint64_t size) const override;
  Sort make_sort(SortKind sk, const SortVec & sorts) const override;

  // AbsSmtSolver's string-value overloads are not declared here, and a
  // declaration of the name would otherwise hide them from lookup on a
  // Yices2 solver. Their default throws NotImplementedException.
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
  // for interacting with third-party Yices2-specific software

  /** @return the context, created on first use; the handle keeps it and the
   *  Yices instance alive, so it stays usable after reset() or this solver's
   *  destruction, though this solver then stops using it. Throws
   *  IncorrectUsageException if Yices rejects the configuration.
   */
  std::shared_ptr<context_t> get_context();

  /** @return the configuration get_context() creates the context from */
  ctx_config_t * get_config();

 protected:
  void do_assert(const Term & t) override;
  Result do_check_sat_assuming(const TermVec & assumptions) override;
  void do_push(uint64_t num) override;
  void do_pop(uint64_t num) override;
  void do_reset() override;
  void do_reset_assertions() override;

  /** Keeps Yices set up. Declared first, so it is destroyed after the
   *  members below that still hold Yices objects.
   */
  Yices2InstanceRef instance = {};

  /** The context, created by get_context() on first use. Yices applies a
   *  configuration only when it creates a context, so the logic and any
   *  option that changes config must be set before then.
   */
  std::shared_ptr<context_t> ctx = nullptr;
  ctx_config_t * config;

  // workaround for: https://github.com/makaimann/smt-switch/issues/218
  uint64_t pushes_after_unsat = 0;  ///< how many pushes after trivial unsat
                                    ///< context status

  double time_limit = 0.0;  ///< in seconds, 0 for none

  // Yices cannot list a context's assertions, so dump_smt2 writes these:
  // the logic given to set_logic, ALL for none, since SMT-LIB declares
  // nothing before set-logic, the formulas asserted and not popped, and
  // how many of them came before each pushed scope
  std::string logic_ = "ALL";
  TermVec assertions = {};
  std::vector<std::size_t> scope_starts = {};

  std::unordered_map<std::string, Term> symbol_table = {};
  ///< Keep track of declared symbols to avoid re-declaration
  ///< Note: Yices2 has a global symbol table, but we want it
  ///< associated with each solver instance. This is why we
  ///< can't rely on yices_get_term_by_name to see if name
  ///< has already been used.

  /** Helper function for managing time limits (if one is set)
   *  Claims the SIGALRM timer, saving the program's handler, and refuses
   *  while the program's own timer is armed.
   */
  void timelimit_start();

  /** Helper function for managing time limits (if one is set)
   *  Restores the program's SIGALRM handler. Returns true iff the query
   *  was terminated due to the time limit.
   */
  bool timelimit_end();
};
}  // namespace smt
