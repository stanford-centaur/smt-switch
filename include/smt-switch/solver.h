/*!
 * \file solver.h
 * \brief Abstract interface for SMT solvers
 * \author Makai Mann
 * \author Clark Barrett
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_SOLVER_H
#define SMT_SWITCH_SOLVER_H

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#include <cstdint>
#include <iterator>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/term_builder.h"

namespace smt {

/**
   Abstract solver class to be implemented by each supported solver.
 */
class AbsSmtSolver : public AbsSmtTermBuilder
{
 public:
  /** @param solver_kind the kind of the underlying solver, which the
   *         derived class (backend implementation) provides
   */
  explicit AbsSmtSolver(SolverKind solver_kind);
  [[deprecated("use the SolverKind constructor")]] explicit AbsSmtSolver(
      SolverEnum se);
  AbsSmtSolver(const AbsSmtSolver & other) = default;
  AbsSmtSolver & operator=(const AbsSmtSolver & other) = default;

  /* Sets a solver option with smt-lib 2 syntax
   * SMTLIB: (set-option :<option> <value>)
   * @param option name of the option
   * @param value string value
   * @throws NotImplementedException for an option the solver does not know
   * @throws IncorrectUsageException for a value the solver does not allow,
   *         or an option it no longer accepts at this point
   */
  virtual void set_opt(const std::string option, const std::string value) = 0;

  /* Sets a solver logic -- see smt-lib 2 logics
   * SMTLIB: (set-logic <logic>)
   * SMT-LIB allows it once, before any declaration, definition, assertion,
   * push or check, and again after reset. Solvers differ on what they
   * accept beyond that: some even after declarations, or more than once.
   * @param logic name of logic
   * @throws NotImplementedException for a logic the solver does not support
   * @throws IncorrectUsageException where the solver no longer accepts a
   *         logic
   */
  virtual void set_logic(const std::string logic) = 0;

  /* Add an assertion to the solver
   * SMTLIB: (assert <t>)
   * The solver does the assertion in do_assert.
   * @param t a boolean term to assert
   * @throws IncorrectUsageException for a term that is not boolean
   */
  void assert_formula(const Term & t);

  /* Check satisfiability of the current assertions
   * SMTLIB: (check-sat)
   * @return a result object - see result.h
   */
  virtual Result check_sat() = 0;

  /* Check satisfiability of the current assertions under the given assumptions
   * Note: an assumption can be any boolean formula, not only a literal as
   * SMT-LIB requires; a solver that needs literals labels the others itself
   * SMTLIB: (check-sat-assuming (t1 t2 ... tn)) with assumptions =
   * [t1,...,tn]
   * The solver does the check in do_check_sat_assuming.
   * @param assumptions a vector of boolean formulas
   * @return a result object - see result.h
   * @throws IncorrectUsageException for an assumption that is not boolean
   */
  Result check_sat_assuming(const TermVec & assumptions);

  /* Check satisfiability under the assumptions in any other range of Terms,
   * such as a TermList or an UnorderedTermSet: any container with begin and
   * end of one type, and C arrays. They are copied into a TermVec, so
   * solvers only override the TermVec version.
   * A single Term is iterable over its children but is not a collection of
   * assumptions, so it is rejected: write { t } to assume just t.
   */
  template <class Range,
            class = std::enable_if_t<
                !std::is_same<Range, Term>::value
                && std::is_constructible<
                    TermVec,
                    decltype(std::begin(std::declval<const Range &>())),
                    decltype(std::end(std::declval<const Range &>()))>::value
                && std::is_convertible<
                    decltype(*std::begin(std::declval<const Range &>())),
                    Term>::value>>
  Result check_sat_assuming(const Range & assumptions)
  {
    return check_sat_assuming(
        TermVec(std::begin(assumptions), std::end(assumptions)));
  }

  [[deprecated("use check_sat_assuming")]] Result check_sat_assuming_list(
      const TermList & assumptions);

  [[deprecated("use check_sat_assuming")]] Result check_sat_assuming_set(
      const UnorderedTermSet & assumptions);

  /* Push contexts
   * SMTLIB: (push <num>)
   * The solver does the push in do_push, and the context level goes up by
   * num once it succeeds.
   * @param num the number of contexts to push
   */
  void push(std::uint64_t num = 1);

  /* Pop contexts
   * SMTLIB: (pop <num>)
   * The solver does the pop in do_pop, and the context level goes down by
   * num once it succeeds.
   * @param num the number of contexts to pop
   * @throws IncorrectUsageException if num is more than the context level
   */
  void pop(std::uint64_t num = 1);

  /** Returns the current context level of the solver
   *  based on the number of pushes/pops since the last reset or
   *  reset_assertions
   *  @return context level
   */
  virtual std::uint64_t get_context_level() const;

  /* Pop all contexts */
  virtual void pop_all();

  /* Get the value of a term after check_sat returns a satisfiable result
   * SMTLIB: (get-value (<t>))
   * @param t the term to get the value of
   * @return a value term
   */
  virtual Term get_value(const Term & t) const = 0;

  /* Get a map of index-value pairs for an array term after check_sat returns
   * sat
   * SMTLIB: (get-value (<t>))
   * @param arr the array to get the value for
   * @param out_const_base a term that will be updated to the const base of the
   * array if there is one. Otherwise, it will be assigned null
   * @return a map of index value pairs for the array
   */
  virtual UnorderedTermMap get_array_values(const Term & arr,
                                            Term & out_const_base) const = 0;

  /** After a call to check_sat_assuming that returns an unsatisfiable result
   *  this function will populate the 'out' UnorderedTermSet with a subset
   *  of the assumptions, as they were given, that are sufficient to make the
   *  assertions unsat.
   *  SMTLIB: (get-unsat-assumptions)
   */
  virtual void get_unsat_assumptions(UnorderedTermSet & out) const = 0;

  /* Return the solver to it's startup state
   * WARNING: This destroys all created terms and sorts
   * SMTLIB: (reset)
   * The solver does the reset in do_reset, and the context level goes back
   * to 0 once it succeeds.
   */
  void reset();

  /* Reset all assertions
   * SMTLIB: (reset-assertions)
   * The solver does the reset in do_reset_assertions, and the context level
   * goes back to 0 once it succeeds.
   */
  void reset_assertions();

  // ------------------------ Optional theories -----------------------------
  // Of the backends here only cvc5 wires up strings, and only cvc5 and Z3
  // datatypes. Each default throws NotImplementedException naming the
  // solver, which a backend without the theory inherits instead of writing
  // the same throw. `AbsTerm::getStringValue` reads a string value back and
  // is defaulted the same way, in term.cpp.

  // Declaring these hides the AbsSmtTermBuilder overloads and templates of
  // the same names
  using AbsSmtTermBuilder::make_sort;
  using AbsSmtTermBuilder::make_term;

  Term make_term(const std::string & s,
                 bool useEscSequences,
                 const Sort & sort) const override;
  Term make_term(const std::wstring & s, const Sort & sort) const override;
  Sort make_sort(const DatatypeDecl & d) const override;
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
  SortVec make_datatype_sorts(
      const std::vector<DatatypeDecl> & decls) const override;

  // extra methods -- not required

  /* Dumps full smt-lib representation of current context to a file */
  virtual void dump_smt2(std::string filename) const;

  /** @return the kind of the underlying solver */
  SolverKind get_kind() const;

  /** @return an enum identifying the underlying solver */
  [[deprecated("use get_kind")]] SolverEnum get_solver_enum() const;

 protected:
  /* Assert a boolean term in the underlying solver; see assert_formula */
  virtual void do_assert(const Term & t) = 0;

  /* Check satisfiability under boolean assumptions in the underlying solver;
   * see check_sat_assuming
   */
  virtual Result do_check_sat_assuming(const TermVec & assumptions) = 0;

  /* Push num contexts in the underlying solver; see push */
  virtual void do_push(std::uint64_t num) = 0;

  /* Pop num contexts in the underlying solver; see pop */
  virtual void do_pop(std::uint64_t num) = 0;

  /* Return the underlying solver to its startup state; see reset */
  virtual void do_reset() = 0;

  /* Drop every assertion and pushed context in the underlying solver; see
   * reset_assertions
   */
  virtual void do_reset_assertions() = 0;

 private:
  SolverKind backend_kind;          ///< the kind of the underlying solver
  std::uint64_t context_level = 0;  ///< pushes minus pops since a reset
};

}  // namespace smt

#endif  // SMT_SWITCH_SOLVER_H
