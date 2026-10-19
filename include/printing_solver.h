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
#include <functional>
#include <ostream>
#include <string>
#include <vector>

#include "interpolating_solver.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"

namespace smt {

/**
 * @deprecated Taken only by the deprecated forms of the printing
 * constructors and factories, which ignore it: a PrintingInterpolator
 * writes each interpolation query as the interpolator it wraps runs it, and
 * nothing a PrintingSolver writes depends on a style.
 */
// the enumerators rather than the type are deprecated, so that the
// deprecated forms can still be defined without a warning
enum PrintingStyleEnum
{
  DEFAULT_STYLE [[deprecated("printing no longer takes a style")]] = 0,
  BZLA_STYLE [[deprecated("printing no longer takes a style")]],
  CVC5_STYLE [[deprecated("printing no longer takes a style")]],
  MSAT_STYLE [[deprecated("printing no longer takes a style")]],
};

/**
 * A class that wraps an SMT-solver and prints corresponding
 * SMT-LIB commands.
 */
class PrintingSolver : public AbsSmtSolver
{
 public:
  PrintingSolver(SmtSolver s, std::ostream * os);
  [[deprecated("use the constructor without a style")]] PrintingSolver(
      SmtSolver s, std::ostream * os, PrintingStyleEnum pse);
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

  /* Operators that are not printed
   * For example, creating terms is not printed, but the
   * created terms will appear in other commands (e.g., assert).
   * */
  Term get_symbol(const std::string & name) override;
  Sort make_sort(const SortKind sk) const override;
  Sort make_sort(const SortKind sk, std::uint64_t size) const override;
  Sort make_sort(const SortKind sk, const SortVec & sorts) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;

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
  Term make_term(const Op op, const TermVec & terms) const override;

 protected:
  void do_push(std::uint64_t num) override;
  void do_pop(std::uint64_t num) override;
  void do_reset() override;
  void do_reset_assertions() override;

  /* The wrapped solver */
  SmtSolver wrapped_solver;
  /* A stream to dump SMT-LIB commands to */
  std::ostream * out_stream;
};

/**
 * A class that wraps an interpolating solver and prints corresponding
 * SMT-LIB commands, writing each interpolation query as the wrapped
 * interpolator runs it, in its backend's syntax. It answers as the wrapped
 * interpolator does.
 */
class PrintingInterpolator : public AbsSmtInterpolator
{
 public:
  PrintingInterpolator(SmtInterpolator s, std::ostream * os);
  [[deprecated("use the constructor without a style")]] PrintingInterpolator(
      SmtInterpolator s, std::ostream * os, PrintingStyleEnum pse);

  Result get_interpolant(const Term & A,
                         const Term & B,
                         Term & out_I) const override;
  Result get_sequence_interpolants(const TermVec & formulae,
                                   TermVec & out_I) const override;
  void set_opt(const std::string option, const std::string value) override;

 protected:
  void do_set_opt(const std::string & option,
                  const std::string & value) override;
  void forget_queries() override;

  /* Prints a query of formulae as the wrapped interpolator runs it, around
   * ask, which runs it and stores its interpolants in out_I; sequence is
   * false for get_interpolant. What the wrapped interpolator keeps from the
   * queries before is followed here, so that only what it actually asks is
   * printed.
   */
  Result print_query(const TermVec & formulae,
                     const TermVec & out_I,
                     bool sequence,
                     const std::function<Result()> & ask) const;

  /* The wrapped interpolator */
  SmtInterpolator wrapped_interpolator;
  /* A stream to dump SMT-LIB commands to */
  std::ostream * out_stream;
  /* Keep track of created names */
  mutable std::size_t num_names = 0;
  /* For Bitwuzla and MathSAT, the formulae left asserted by the last query,
   * one context level each, and the names they were printed with */
  mutable TermVec asserted;
  mutable std::vector<std::string> asserted_names;
  /* For cvc5, the last sequence query if it was unsat, whose interpolants
   * cvc5 reuses for a sequence query that extends it */
  mutable TermVec last_unsat_query;
};

/* Returns a printing SmtSolver by wrapping PrintingSmtSolver's constructor.
 * @param wrapped_solver the solver to wrap
 * @param out_stream the stream to dump SMT-LIB to
 * @return an SmtSolver that dumps to out_stream each command that is executed.
 */
SmtSolver create_printing_solver(SmtSolver wrapped_solver,
                                 std::ostream * out_stream);

/* As create_printing_solver(wrapped_solver, out_stream); style is ignored.
 */
[[deprecated("use create_printing_solver without a style")]] SmtSolver
create_printing_solver(SmtSolver wrapped_solver,
                       std::ostream * out_stream,
                       PrintingStyleEnum style);

/* Returns a printing SmtInterpolator by wrapping PrintingInterpolator's
 * constructor.
 * @param wrapped_interpolator the interpolating solver to wrap
 * @param out_stream the stream to dump SMT-LIB to
 * @return an SmtInterpolator that dumps to out_stream each command that is
 *         executed, writing each interpolation query as wrapped_interpolator
 *         runs it, and answers as wrapped_interpolator does
 */
SmtInterpolator create_printing_interpolator(
    SmtInterpolator wrapped_interpolator, std::ostream * out_stream);

/* As create_printing_interpolator(wrapped_interpolator, out_stream); style
 * is ignored.
 */
[[deprecated("use create_printing_interpolator without a style")]]
SmtInterpolator create_printing_interpolator(
    SmtInterpolator wrapped_interpolator,
    std::ostream * out_stream,
    PrintingStyleEnum style);

}  // namespace smt
