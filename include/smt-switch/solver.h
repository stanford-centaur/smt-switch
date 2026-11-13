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

#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {

/**
   Abstract solver class to be implemented by each supported solver.

   Terms and sorts keep alive the backend state they point into, so they can
   still be used after their solver is destroyed.
 */
class AbsSmtSolver
{
 public:
  /** SolverEnum identifies which underlying solver is being used.
   *  It is provided by the derived class (backend implementation)
   */
  explicit AbsSmtSolver(SolverEnum se);
  AbsSmtSolver(const AbsSmtSolver & other) = default;
  AbsSmtSolver & operator=(const AbsSmtSolver & other) = default;
  virtual ~AbsSmtSolver() = default;

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

  /* Declare an uninterpreted sort, or a sort constructor if arity is nonzero
   * SMTLIB: (declare-sort <name> <arity>)
   * @param name the name of the sort
   * @param arity the arity of the sort
   * @return a Sort object
   */
  virtual Sort make_sort(const std::string name, std::uint64_t arity) const = 0;

  /* Create a sort
   * @param sk the SortKind (BOOL, INT, REAL)
   * @return a Sort object
   */
  virtual Sort make_sort(const SortKind sk) const = 0;

  /* Create a sort
   * @param sk the SortKind (BV)
   * @param size (e.g. bitvector width for BV SortKind)
   * @return a Sort object
   */
  virtual Sort make_sort(const SortKind sk, std::uint64_t size) const = 0;

  /* Create a sort from sort parameters
   * @param sk the SortKind (ARRAY, FUNCTION)
   * @param sorts for ARRAY, the index sort then the element sort; for
   * FUNCTION, the domain sorts then the codomain sort
   * @return a Sort object
   * This is the overload a backend implements; the one taking the sorts as
   * separate arguments below is a shorthand for it.
   */
  virtual Sort make_sort(const SortKind sk, const SortVec & sorts) const = 0;

  /* Shorthand for make_sort(sk, SortVec{ sort1, sorts... })
   * e.g. make_sort(ARRAY, index, element) or make_sort(FUNCTION, d1, d2, cod)
   * No SortKind takes a single sort parameter yet.
   */
  template <typename... Sorts,
            typename = std::enable_if_t<
                (std::is_convertible_v<const Sorts &, Sort> && ...)>>
  Sort make_sort(const SortKind sk,
                 const Sort & sort1,
                 const Sorts &... sorts) const
  {
    return make_sort(sk, SortVec{ sort1, sorts... });
  }

  /* Apply a sort constructor to sorts
   * SMTLIB: ( <identifier> <sort>+ ), for instance (List Int)
   * @param sort_con a sort with SortKind UNINTERPRETED_CONS (must have
   * nonzero arity)
   * @param sorts a vector of sorts of size matching sort_con->get_arity()
   * @return a Sort object
   */
  virtual Sort make_sort(const Sort & sort_con,
                         const SortVec & sorts) const = 0;

  /* Make a boolean value term
   * @param b boolean value
   * @return a value term with Sort BOOL and value b
   */
  virtual Term make_term(bool b) const = 0;

  /* Make a bit-vector, int or real value term
   * @param i the value
   * @param sort the sort to create
   * @return a value term with Sort sort and value i
   */
  virtual Term make_term(std::int64_t i, const Sort & sort) const = 0;

  /* Make a bit-vector, int, real or (in the future) string value term
   * @param val the numeric value as a string, or a string value
   * @param sort the sort to create
   * @param base the base val is written in, from 2 to 36, for the digits (0
   * to 9, then a to z in either case) of a numeral and of each part of a
   * decimal or fraction
   * @return a value term with Sort sort and value val
   */
  virtual Term make_term(const std::string val,
                         const Sort & sort,
                         std::uint64_t base = 10) const = 0;

  /* Make a value of a particular sort, such as constant arrays
   * @param val the Term used to create the value (.e.g constant array with 0)
   * @param sort the sort of value to create
   * @return a value term with Sort sort
   */
  virtual Term make_term(const Term & val, const Sort & sort) const = 0;

  /* Make a symbolic constant or function term
   * SMTLIB: (declare-fun <name> (s1 ... sn) s) where sort = s1x...xsn -> s
   * @param name the name of constant or function
   * @param sort the sort of this constant or function
   * @return the symbolic constant or function term
   */
  virtual Term make_symbol(const std::string name, const Sort & sort) = 0;

  /** Look up a symbol by name.
   *  If no symbol of that name has been declared, throws
   *  IncorrectUsageException
   *
   *  Allows a user to look up a symbol by name. This can be very useful for
   * term translation, since we can look up symbols instead of keeping track of
   * the mapping via externally populated caches (in the case where the target
   *  solver has already been used).
   *
   *  Note, solver backend deals with the implementation. The main motivation
   * for this is that each backend solver has to own the symbol table. If the
   * symbol table were stored in AbsSmtSolver then it would get destructed after
   * the backend solver which has bad refcounting implications for many solvers.
   *
   *  @param name the name of the symbol to look up
   *  @return the Term representation of the corresponding symbol
   */
  virtual Term get_symbol(const std::string & name) const = 0;

  /* Make a parameter term to be bound by a quantifier
   * @param name the name of the parameter
   * @param sort the sort of this parameter
   * @return the parameter term
   */
  virtual Term make_param(const std::string name, const Sort & sort) const = 0;

  /* Make a new term
   * @param op the operator to use
   * @param terms vector of children
   * @return the created term
   * This is the overload a backend implements; the one taking the children
   * as separate arguments below is a shorthand for it.
   */
  virtual Term make_term(const Op op, const TermVec & terms) const = 0;

  /* Shorthand for make_term(op, TermVec{ t, ts... })
   * e.g. make_term(Not, a), make_term(Equal, a, b) or make_term(And, a, b, c)
   */
  template <typename... Terms,
            typename = std::enable_if_t<
                (std::is_convertible_v<const Terms &, Term> && ...)>>
  Term make_term(const Op op, const Term & t, const Terms &... ts) const
  {
    return make_term(op, TermVec{ t, ts... });
  }
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

  // ---------------------------- Strings ------------------------------------
  // Of the backends here only cvc5 wires up the string theory, so neither of
  // these is pure virtual. Each default lives in solver.cpp and throws
  // NotImplementedException naming the solver. `AbsTerm::getStringValue`
  // reads a string value back and is defaulted the same way, in term.cpp.

  /* Make a string value term from an `std::string` which may contain SMT-LIB
   * compatible escape sequences like `\u1000` or `\u{20}` to encode unicode
   * characters.
   * @param s is the value
   * @param useEscSequences determines whether escape sequence in `s` should
   * be converted to the corresponding unicode character
   * @param sort the sort to create
   * @return a value term with Sort sort and value s
   */
  virtual Term make_term(const std::string & s,
                         bool useEscSequences,
                         const Sort & sort) const;

  /* Make a string value term
   * @param s is the value
   * @param sort the sort to create
   * @return a value term with Sort sort and value s
   */
  virtual Term make_term(const std::wstring & s, const Sort & sort) const;

  // --------------------------- Datatypes ----------------------------------
  // Algebraic datatypes have been standard SMT-LIB since 2.6, but only cvc5
  // and Z3 support them. So none of these is pure virtual. Each default lives
  // in solver.cpp and throws NotImplementedException naming the solver, which
  // a backend without datatypes inherits instead of writing the same throw.

  /* Create a datatype sort
   * @param d the Datatype Declaration
   * @return a Sort object
   */
  virtual Sort make_sort(const DatatypeDecl & d) const;

  /* Initialize a datatype declaration with some name
   * @param s Name of the datatype
   * @return an empty Datatype declaration
   */
  virtual DatatypeDecl make_datatype_decl(const std::string & s) const;

  /* Initialize a datatype constructor declaration with some name
   * @param s Name of the datatype constructor
   * @return an empty Datatype declaration
   */
  virtual DatatypeConstructorDecl make_datatype_constructor_decl(
      const std::string s) const;

  /* Add a datatype constructor to a datatype declaration
   * @param dt Datatype
   * @param con Datatype constructor
   */
  virtual void add_constructor(DatatypeDecl & dt,
                               const DatatypeConstructorDecl & con) const;

  /* Add a selector to a datatype constructor
   * @param dt DatatypeConstructorDecl
   * @param name name of the selector
   * @param s sort of the selector
   */

  virtual void add_selector(DatatypeConstructorDecl & dt,
                            const std::string & name,
                            const Sort & s) const;

  /* Add a selector to a datatype constructor where the sort is the datatype
   * itself (whose sort doesn't exist yet)
   * @param dt DatatypeConstructorDecl
   * @param name name of the selector
   */
  virtual void add_selector_self(DatatypeConstructorDecl & dt,
                                 const std::string & name) const;

  /* get a term representing to a datatype constructor
   * @param s A datatype sort (error otherwise)
   * @param name name of the constructor
   */

  virtual Term get_constructor(const Sort & s, std::string name) const;

  /* get a term representing to a datatype tester
   * @param s A datatype sort (error otherwise)
   * @param name name of the constructor
   */

  virtual Term get_tester(const Sort & s, std::string name) const;

  /* get a term representing to a datatype selector
   * @param s A datatype sort (error otherwise)
   * @param con name of the constructor
   * @param name name of the selector
   */
  virtual Term get_selector(const Sort & s,
                            std::string con,
                            std::string name) const;

  /** Create sorts for the corresponding DatatypeDecls.
   *
   *  @param decls the datatype decls
   *  @return one datatype sort per declaration, in the same order
   */
  virtual SortVec make_datatype_sorts(
      const std::vector<DatatypeDecl> & decls) const;

  /** Convenience function that calls make_datatype_sorts with a single sort. */
  Sort make_datatype_sort(const DatatypeDecl & decl) const;

  // Methods implemented at the abstract level
  // Note: These can be overloaded in the specific solver implementation for
  //       performance improvements

  /* Substitute all symbolic constants with terms in all subterms
   *   using the provided mapping
   * @param term the term to apply substitution map to
   * @param substitution_map the map to use for substitution
   * @return the term with the substitution map applied
   */
  virtual Term substitute(const Term term,
                          const UnorderedTermMap & substitution_map) const;

  virtual TermVec substitute_terms(
      const TermVec & terms, const UnorderedTermMap & substitution_map) const;

  // extra methods -- not required

  /* Dumps full smt-lib representation of current context to a file */
  virtual void dump_smt2(std::string filename) const;

  /** @return an enum identifying the underlying solver */
  SolverEnum get_solver_enum() const;

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

  SolverEnum solver_enum;  ///< an enum identifying the underlying solver

 private:
  std::uint64_t context_level = 0;  ///< pushes minus pops since a reset
};

}  // namespace smt

#endif  // SMT_SWITCH_SOLVER_H
