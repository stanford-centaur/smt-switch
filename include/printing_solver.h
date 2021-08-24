/*********************                                                        */
/*! \file printing_solver.h
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class that wraps another SmtSolver and dumps SMT-LIB
**        that corresponds to the operations being performed.
**/

#pragma once

#include "solver.h"
#include "term_hashtable.h"

namespace smt {

/**
 * Solvers may differ in the style of their expected SMT-LIB dumped files.
 * Generally, this can include dagification, define-fun's etc.
 * Concretely, we currently only consider different syntaxes of 
 * getting interpolants in SMT-LIB-like fashion.
 * Currently interpolation is only supported for mathsat, but this enum
 * will be used for other solvers as well
 */
enum PrintingStyleEnum
{
  DEFAULT_STYLE = 0,
  CVC4_STYLE,
  MSAT_STYLE,
};

/**
 * A class that wraps an SMT-solver and prints corresponding
 * SMT-LIB commands.
 */
class PrintingSolver : public AbsSmtSolver
{
 public:
  PrintingSolver(SmtSolver s, std::ostream*, PrintingStyleEnum pse); 
  ~PrintingSolver();

  /* Operators that are printed */
  Sort make_sort(const std::string name, uint64_t arity) const override;
  Term make_symbol(const std::string name, const Sort & sort) override;
  Term make_param(const std::string name, const Sort & sort) override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) override;
  void reset() override;
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  void push(uint64_t num = 1) override;
  void pop(uint64_t num = 1) override;
  uint64_t get_context_level() const override;
  void reset_assertions() override;
  Result get_interpolant(const Term & A,
                         const Term & B,
                         Term & out_I) const override;

  /* Operators that are not printed 
   * For example, creating terms is not printed, but the
   * created terms will appear in other commands (e.g., assert). 
   * */
  Term get_symbol(const std::string & name) override;
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
  Term make_term(const std::string val,
                 const Sort & sort,
                 uint64_t base = 10) const override;
  Term make_term(const Term & val, const Sort & sort) const override;
  Term make_term(const Op op, const Term & t) const override;
  Term make_term(const Op op, const Term & t0, const Term & t1) const override;
  Term make_term(const Op op,
                 const Term & t0,
                 const Term & t1,
                 const Term & t2) const override;
  Term make_term(const Op op, const TermVec & terms) const override;



 protected:
  /* The wrapped solver */
  SmtSolver wrapped_solver;  
  /* A stream to dump SMT-LIB commands to */
  std::ostream* out_stream; 
  /* A style to use while printing */
  PrintingStyleEnum style;
};

/* Returns a printing SmtSolver by wrapping PrintingSmtSolver's constructor.
 * @param wrapped_solver the solver to wrap
 * @param out_stream the stream to dump SMT-LIB to
 * @param style the printing style
 * @return an SmtSolver that dumps to out_stream each command that is executed.
 */

SmtSolver create_printing_solver(SmtSolver wrapped_solver, std::ostream* out_stream, PrintingStyleEnum style);

}  // namespace smt
