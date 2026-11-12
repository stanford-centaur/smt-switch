/*!
 * \file printing_solver.h
 * \brief Class that wraps another SmtSolver and dumps SMT-LIB that corresponds
 *        to the operations being performed
 * \author Yoni Zohar
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_PRINTING_SOLVER_H
#define SMT_SWITCH_PRINTING_SOLVER_H

#include <cstdint>
#include <ostream>
#include <string>
#include <vector>

#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

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
  PrintingSolver(const PrintingSolver & other) = default;
  PrintingSolver(PrintingSolver && other) = default;
  PrintingSolver & operator=(const PrintingSolver & other) = default;
  PrintingSolver & operator=(PrintingSolver && other) = default;

  /* Operators that are printed */
  // Declaring make_sort here at all would hide AbsSmtSolver's convenience
  // overloads from lookup on this type, so name them back in.
  using AbsSmtSolver::make_sort;
  Sort make_sort(const std::string name, std::uint64_t arity) const override;
  Sort make_sort(const DatatypeDecl & d) const override;
  SortVec make_datatype_sorts(
      const std::vector<DatatypeDecl> & decls) const override;
  Term make_symbol(const std::string name, const Sort & sort) override;
  Term make_param(const std::string name, const Sort & sort) const override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) const override;
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  Result check_sat() override;
  std::uint64_t get_context_level() const override;
  void dump_smt2(std::string filename) const override;

  /* Operators that are not printed
   * For example, creating terms is not printed, but the
   * created terms will appear in other commands (e.g., assert).
   * */
  Term get_symbol(const std::string & name) const override;
  Sort make_sort(const SortKind sk) const override;
  Sort make_sort(const SortKind sk, std::uint64_t size) const override;
  Sort make_sort(const SortKind sk, const SortVec & sorts) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;
  // datatype declarations are recorded, and printed when their sort is made
  DatatypeDecl make_datatype_decl(const std::string & s) const override;
  DatatypeConstructorDecl make_datatype_constructor_decl(
      const std::string s) const override;
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
  void do_assert(const Term & t) override;
  Result do_check_sat_assuming(const TermVec & assumptions) override;
  void do_push(std::uint64_t num) override;
  void do_pop(std::uint64_t num) override;
  void do_reset() override;
  void do_reset_assertions() override;

  /* The wrapped solver */
  SmtSolver wrapped_solver;
  /* A stream to dump SMT-LIB commands to */
  std::ostream * out_stream;
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

}  // namespace smt

#endif  // SMT_SWITCH_PRINTING_SOLVER_H
