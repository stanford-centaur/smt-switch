/*********************                                                        */
/*! \file cvc5_solver.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief cvc5 implementation of AbsSmtSolver
**
**
**/

#pragma once

#include <limits>
#include <memory>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "cvc5/cvc5.h"
#include "cvc5_datatype.h"
#include "cvc5_sort.h"
#include "cvc5_term.h"
#include "datatype.h"
#include "exceptions.h"
#include "ops.h"
#include "result.h"
#include "smt.h"
#include "sort.h"
#include "term.h"

namespace smt {
/**
   cvc5 Solver
 */
class Cvc5Solver : public AbsSmtSolver
{
 public:
  Cvc5Solver() : AbsSmtSolver(CVC5), solver(), context_level(0)
  {
    solver.setOption("lang", "smt2");
    solver.setOption("bv-print-consts-as-indexed-symbols", "true");
    solver.setOption("arrays-exp", "true");
  };
  Cvc5Solver(const Cvc5Solver &) = delete;
  Cvc5Solver & operator=(const Cvc5Solver &) = delete;
  ~Cvc5Solver(){};
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

  // helpers
  ::cvc5::Op make_cvc5_op(Op op) const;

  // getters for solver-specific objects
  // for interacting with third-party cvc5-specific software
  ::cvc5::Solver & get_cvc5_solver() { return solver; };
  
 protected:
  ::cvc5::Solver solver;

  std::unordered_map<std::string, Term> symbol_table;

  uint64_t context_level;

  // helper function
  inline Result check_sat_assuming(const std::vector<cvc5::Term> & cvc5assumps)
  {
    ::cvc5::Result r = solver.checkSatAssuming(cvc5assumps);
    if (r.isUnsat())
    {
      return Result(UNSAT);
    }
    else if (r.isSat())
    {
      return Result(SAT);
    }
    else if (r.isUnknown())
    {
      std::stringstream ss;
      ss << r.getUnknownExplanation();
      return Result(UNKNOWN, ss.str());
    }
    else
    {
      throw NotImplementedException("Unimplemented result type from cvc5");
    }
  }
};

// Interpolating Solver
class cvc5InterpolatingSolver : public Cvc5Solver
{
 public:
  cvc5InterpolatingSolver() {}
  cvc5InterpolatingSolver(const cvc5InterpolatingSolver &) = delete;
  cvc5InterpolatingSolver & operator=(const cvc5InterpolatingSolver &) = delete;
  ~cvc5InterpolatingSolver() {}

  Result get_interpolant(const Term & A,
                         const Term & B,
                         Term & out_I) const override;
};

}  // namespace smt
