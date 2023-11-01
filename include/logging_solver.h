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

#include "solver.h"
#include "term_hashtable.h"

#include <string>

namespace smt {

class LoggingSolver : public AbsSmtSolver
{
 public:
  LoggingSolver(SmtSolver s);
  ~LoggingSolver();

  // implemented
  Sort make_sort(const std::string name, uint64_t arity) const override;
  Sort make_sort(const SortKind sk) const override;
  Sort make_sort(const SortKind sk, uint64_t size) const override;
  Sort make_sort(const SortKind sk, const Sort & sort1) const override;
  Sort make_sort(const SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2) const override;
  Sort make_sort(const SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2,
                 const Sort & sort3) const override;
  Sort make_sort(const SortKind sk, const SortVec & sorts) const override;
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
  Term make_term(const std::string& s, bool useEscSequences, const Sort & sort) const override;
  Term make_term(const std::wstring& s, const Sort & sort) const override;
  Term make_term(const std::string val,
                 const Sort & sort,
                 uint64_t base = 10) const override;
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
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) override;
  // Will probably remove this eventually
  // For now, need to clear the hash table
  void reset() override;

  // dispatched to underlying solver
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  Result check_sat_assuming_list(const TermList & assumptions) override;
  Result check_sat_assuming_set(const UnorderedTermSet & assumptions) override;
  void push(uint64_t num = 1) override;
  void pop(uint64_t num = 1) override;
  uint64_t get_context_level() const override;
  void reset_assertions() override;

 protected:
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
  mutable size_t next_term_id;  ///< used to give LoggingTerms a unique id
};

}  // namespace smt
