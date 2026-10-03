/*********************                                                        */
/*! \file bitwuzla_solver.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Po-Chun Chien
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bitwuzla implementation of AbsSmtSolver
**
**
**/

#pragma once

#include <cassert>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "bitwuzla/cpp/bitwuzla.h"
#include "bitwuzla_term.h"
#include "interpolating_solver.h"
#include "result.h"
#include "smt.h"
#include "utils.h"

namespace smt {

/**
   Bzla Solver
 */
class BzlaSolver : public AbsSmtSolver
{
 public:
  BzlaSolver();
  BzlaSolver(const BzlaSolver &) = delete;
  BzlaSolver & operator=(const BzlaSolver &) = delete;
  ~BzlaSolver();
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
  std::uint64_t get_context_level() const override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) override;

  // The datatype methods are left to AbsSmtSolver, whose defaults throw.
  // Declaring make_sort here at all would hide AbsSmtSolver's own overloads
  // from lookup on this type, so name them back in.
  using AbsSmtSolver::make_sort;
  Sort make_sort(const std::string name, std::uint64_t arity) const override;
  Sort make_sort(SortKind sk) const override;
  Sort make_sort(SortKind sk, std::uint64_t size) const override;
  Sort make_sort(SortKind sk, const SortVec & sorts) const override;

  // AbsSmtSolver's string-value overloads are not declared here, and a
  // declaration of the name would otherwise hide them from lookup on a
  // Bitwuzla solver. Their default throws NotImplementedException.
  using AbsSmtSolver::make_term;
  Term make_term(bool b) const override;
  Term make_term(std::int64_t i, const Sort & sort) const override;
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
  TermVec substitute_terms(
      const TermVec & term,
      const UnorderedTermMap & substitution_map) const override;
  void dump_smt2(std::string filename) const override;

  // getters for solver-specific objects
  // for interacting with third-party Bitwuzla-specific software
  // creates the Bitwuzla instance if it does not exist yet
  bitwuzla::Bitwuzla * get_bitwuzla() const;

 protected:
  bitwuzla::Options options;
  // bzla uses tm, so tm is declared first and outlives it
  std::unique_ptr<bitwuzla::TermManager> tm;
  mutable std::unique_ptr<bitwuzla::Bitwuzla> bzla;

  std::unordered_map<std::string, Term> symbol_table;
  std::uint64_t context_level;

  // helper functions
  template <class T>
  inline Result check_sat_assuming_internal(T container)
  {
    std::shared_ptr<BzlaTerm> bt;
    std::vector<bitwuzla::Term> assumptions;
    for (auto && t : container)
    {
      bt = std::static_pointer_cast<BzlaTerm>(t);
      assumptions.push_back(bt->term);
    }

    bitwuzla::Result res;
    try
    {
      res = get_bitwuzla()->check_sat(assumptions);
    }
    catch (std::exception & e)
    {
      throw InternalSolverException(e.what());
    }

    if (res == bitwuzla::Result::SAT)
    {
      return Result(SAT);
    }
    else if (res == bitwuzla::Result::UNSAT)
    {
      return Result(UNSAT);
    }
    else
    {
      assert(res == bitwuzla::Result::UNKNOWN);
      return Result(UNKNOWN);
    }
  }
};

class BzlaInterpolatingSolver : public AbsSmtInterpolator
{
 public:
  BzlaInterpolatingSolver();
  BzlaInterpolatingSolver(const BzlaInterpolatingSolver &) = delete;
  BzlaInterpolatingSolver & operator=(const BzlaInterpolatingSolver &) = delete;

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
  std::shared_ptr<BzlaSolver> bzla_solver;

  // assertions from the last interpolation query, indexed by the context level
  // (although one can get assertions using `bzla->get_assertions()`,
  // the method does not guarantee that the assertions are in the correct order)
  mutable TermVec last_itp_query_assertions;

  inline static const std::unordered_set<std::string> disallowed_options = {
    "produce-interpolants"
  };
  bool incremental_mode = true;
  std::string dump_queries_prefix = "";
  mutable uint32_t itp_query_count = 0;
};

}  // namespace smt
