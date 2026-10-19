/*********************                                                        */
/*! \file logging_solver.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class that wraps another SmtSolver and tracks the term DAG by
**        wrapping sorts and terms and performs hash-consing.
**
**/

#pragma once

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"
#include "term_hashtable.h"

namespace smt {

class LoggingDatatypeConstructorDecl;

class LoggingSolver : public AbsSmtSolver
{
 public:
  LoggingSolver(SmtSolver s);

  // implemented
  // Declaring make_sort here at all would hide AbsSmtSolver's convenience
  // overloads from lookup on this type, so name them back in.
  using AbsSmtSolver::make_sort;
  Sort make_sort(const std::string name, std::uint64_t arity) const override;
  Sort make_sort(const SortKind sk) const override;
  Sort make_sort(const SortKind sk, std::uint64_t size) const override;
  Sort make_sort(const SortKind sk, const SortVec & sorts) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;

  // datatypes, recorded so that their components get logging sorts
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

  // Declaring make_term here hides the AbsSmtSolver template that takes
  // the children as separate arguments, so name it back in.
  using AbsSmtSolver::make_term;
  Term make_term(bool b) const override;
  Term make_term(std::int64_t i, const Sort & sort) const override;
  Term make_term(const std::string & s,
                 bool useEscSequences,
                 const Sort & sort) const override;
  Term make_term(const std::wstring & s, const Sort & sort) const override;
  Term make_term(const std::string val,
                 const Sort & sort,
                 std::uint64_t base = 10) const override;
  Term make_term(const Term & val, const Sort & sort) const override;
  Term make_symbol(const std::string name, const Sort & sort) override;
  Term get_symbol(const std::string & name) override;
  Term make_param(const std::string name, const Sort & sort) override;
  Term make_term(const Op op, const TermVec & terms) const override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) override;

  // dispatched to underlying solver
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  // Overriding check_sat_assuming hides the AbsSmtSolver template that
  // takes any range of Terms, so name it back in.
  using AbsSmtSolver::check_sat_assuming;
  Result check_sat_assuming(const TermVec & assumptions) override;
  std::uint64_t get_context_level() const override;
  void dump_smt2(std::string filename) const override;

 protected:
  void do_push(std::uint64_t num) override;
  void do_pop(std::uint64_t num) override;
  void do_reset() override;
  void do_reset_assertions() override;

  /** The recorded declaration of a datatype sort's constructor
   *  @param s a datatype sort made by this solver
   *  @param name the name of the constructor
   *  @return its declaration, as this solver recorded it
   */
  std::shared_ptr<LoggingDatatypeConstructorDecl> find_constructor(
      const Sort & s, const std::string & name) const;

  /** Wraps a constructor, selector or tester term of the underlying solver
   *  @param wrapped the underlying term
   *  @param sk CONSTRUCTOR, SELECTOR or TESTER
   *  @param domain the logging sorts of its arguments
   *  @param codomain the logging sort of its result
   *  @param repr how it prints in SMT-LIB
   *  @return the hash-consed logging term
   */
  Term make_component(const Term & wrapped,
                      SortKind sk,
                      const SortVec & domain,
                      const Sort & codomain,
                      const std::string & repr) const;

  SmtSolver wrapped_solver;  ///< the underlying solver
  std::unique_ptr<TermHashTable> hashtable;

  std::unordered_map<std::string, Term> symbol_table;

  // stores a mapping from wrapped terms to logging terms
  // that were used in check_sat_assuming
  // this is so they can be recovered with the correct children/op
  // after a call to get_unsat_assumptions
  std::unique_ptr<UnorderedTermMap> assumption_cache;

  // NOTE this is a little ugly, but this needs to be incremented
  // in const methods (make_term), so it is marked mutable
  // this was better than making them non-const because most solvers
  // can respect the const-ness of those make_term functions
  mutable std::size_t next_term_id;  ///< used to give LoggingTerms a unique id
};

}  // namespace smt
