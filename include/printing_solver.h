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

#include <cstddef>
#include <cstdint>
#include <ostream>
#include <string>

#include "interpolating_solver.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"

namespace smt {

/**
 * Solvers may differ in the style of their expected SMT-LIB dumped files.
 * Generally, this can include dagification, define-fun's etc.
 * Concretely, we currently only consider different syntaxes of
 * getting interpolants in SMT-LIB-like fashion.
 * Bitwuzla, cvc5 and MathSAT each have their own style, and a
 * PrintingInterpolator needs one of those three.
 */
enum PrintingStyleEnum
{
  DEFAULT_STYLE = 0,
  BZLA_STYLE,
  CVC5_STYLE,
  MSAT_STYLE,
};

/**
 * A class that wraps an SMT-solver and prints corresponding
 * SMT-LIB commands.
 */
class PrintingSolver : public AbsSmtSolver
{
 public:
  PrintingSolver(SmtSolver s, std::ostream *, PrintingStyleEnum pse);
  ~PrintingSolver();

  /* Operators that are printed */
  // The datatype methods are left to AbsSmtSolver, whose defaults throw.
  // Declaring make_sort here at all would hide AbsSmtSolver's own overloads
  // from lookup on this type, so name them back in.
  using AbsSmtSolver::make_sort;
  Sort make_sort(const std::string name, std::uint64_t arity) const override;
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
  // Overriding check_sat_assuming hides the AbsSmtSolver template that
  // takes any range of Terms, so name it back in.
  using AbsSmtSolver::check_sat_assuming;
  Result check_sat_assuming(const TermVec & assumptions) override;
  void push(std::uint64_t num = 1) override;
  void pop(std::uint64_t num = 1) override;
  std::uint64_t get_context_level() const override;
  void reset_assertions() override;

  /* Operators that are not printed
   * For example, creating terms is not printed, but the
   * created terms will appear in other commands (e.g., assert).
   * */
  Term get_symbol(const std::string & name) override;
  Sort make_sort(const SortKind sk) const override;
  Sort make_sort(const SortKind sk, std::uint64_t size) const override;
  Sort make_sort(const SortKind sk, const SortVec & sorts) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;

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
  std::ostream * out_stream;
  /* A style to use while printing */
  PrintingStyleEnum style;
};

/**
 * A class that wraps an interpolating solver and prints corresponding
 * SMT-LIB commands, writing each interpolation query in the given style.
 */
class PrintingInterpolator : public AbsSmtInterpolator
{
 public:
  PrintingInterpolator(SmtInterpolator s,
                       std::ostream * os,
                       PrintingStyleEnum pse);

  Result get_interpolant(const Term & A,
                         const Term & B,
                         Term & out_I) const override;
  Result get_sequence_interpolants(const TermVec & formulae,
                                   TermVec & out_I) const override;
  void set_opt(const std::string option, const std::string value) override;
  void reset() override;
  void reset_assertions() override;

 protected:
  /* The wrapped interpolator */
  SmtInterpolator wrapped_interpolator;
  /* A stream to dump SMT-LIB commands to */
  std::ostream * out_stream;
  /* A style to use while printing */
  PrintingStyleEnum style;
  /* Keep track of created names */
  mutable std::size_t num_names = 0;
};

/* Returns a printing SmtSolver by wrapping PrintingSmtSolver's constructor.
 * @param wrapped_solver the solver to wrap
 * @param out_stream the stream to dump SMT-LIB to
 * @param style the printing style
 * @return an SmtSolver that dumps to out_stream each command that is executed.
 */

SmtSolver create_printing_solver(SmtSolver wrapped_solver,
                                 std::ostream * out_stream,
                                 PrintingStyleEnum style);

/* Returns a printing SmtInterpolator by wrapping PrintingInterpolator's
 * constructor.
 * @param wrapped_interpolator the interpolating solver to wrap
 * @param out_stream the stream to dump SMT-LIB to
 * @param style the printing style, which decides how interpolation queries
 *        are written: BZLA_STYLE, CVC5_STYLE or MSAT_STYLE
 * @return an SmtInterpolator that dumps to out_stream each command that is
 *         executed.
 * @throws IncorrectUsageException for any other style
 */
SmtInterpolator create_printing_interpolator(
    SmtInterpolator wrapped_interpolator,
    std::ostream * out_stream,
    PrintingStyleEnum style);

}  // namespace smt
