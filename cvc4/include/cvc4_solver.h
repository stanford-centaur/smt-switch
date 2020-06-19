/*********************                                                        */
/*! \file cvc4_solver.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief CVC4 implementation of AbsSmtSolver
**
**
**/

#ifndef SMT_CVC4_SOLVER_H
#define SMT_CVC4_SOLVER_H

#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "cvc4_sort.h"
#include "cvc4_term.h"
#include "cvc4_datatype.h"

#include "api/cvc4cpp.h"

#include "exceptions.h"
#include "ops.h"
#include "result.h"
#include "smt.h"
#include "sort.h"
#include "term.h"
#include "datatype.h"

namespace smt {
/**
   CVC4 Solver
 */
class CVC4Solver : public AbsSmtSolver
{
 public:
  CVC4Solver() : AbsSmtSolver(CVC4), solver()
  {
    solver.setOption("lang", "smt2");
  };
  CVC4Solver(const CVC4Solver &) = delete;
  CVC4Solver & operator=(const CVC4Solver &) = delete;
  ~CVC4Solver() { };
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  void push(uint64_t num = 1) override;
  void pop(uint64_t num = 1) override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  TermVec get_unsat_core() override;
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
  Sort make_sort(const DatatypeDecl & d) const override;

  DatatypeDecl make_datatype_decl(const std::string & s) override;
  DatatypeConstructorDecl make_datatype_constructor_decl(const std::string s) const override;
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
  void dump_smt2(std::string filename) const override;
  // helpers
  ::CVC4::api::Op make_cvc4_op(Op op) const;

 protected:
  ::CVC4::api::Solver solver;
  // keep track of created symbols
  std::unordered_map<std::string, Term> symbols;
};

//Interpolating Solver
class CVC4InterpolatingSolver : public CVC4Solver
{
  public: 
    CVC4InterpolatingSolver() {}
    CVC4InterpolatingSolver(const CVC4InterpolatingSolver &) = delete;
    CVC4InterpolatingSolver & operator=(const CVC4InterpolatingSolver &) = delete;
    ~CVC4InterpolatingSolver() {}

  bool get_interpolant(const Term & A,
                       const Term & B,
                       Term & out_I) const override;
};

}  // namespace smt

#endif
