/*********************                                                        */
/*! \file solver.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Abstract interface for SMT solvers.
**
**
**/

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#pragma once

#include <cstdint>
#include <iterator>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>
#if __has_include(<version>)
#include <version>
#endif
#if defined(__cpp_lib_ranges) && defined(__cpp_concepts)
#include <ranges>
#endif

#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"

namespace smt {

namespace detail {

// begin and end of a range, looked up as a range-based for loop does
#if defined(__cpp_lib_ranges) && defined(__cpp_concepts)
template <class C>
auto range_begin(C & c)
{
  return std::ranges::begin(c);
}

template <class C>
auto range_end(C & c)
{
  return std::ranges::end(c);
}
#else
using std::begin;
using std::end;

template <class C>
auto range_begin(C & c) -> decltype(begin(c))
{
  return begin(c);
}

template <class C>
auto range_end(C & c) -> decltype(end(c))
{
  return end(c);
}

// The C++17 counterpart of the C++20 constraints on check_sat_assuming: R
// has begin and end of one input iterator type, which yields Terms.
template <class R, class = void>
struct is_term_range : std::false_type
{
};

template <class R>
struct is_term_range<
    R,
    std::enable_if_t<
        std::is_same<decltype(range_begin(std::declval<R>())),
                     decltype(range_end(std::declval<R>()))>::value
        && std::is_base_of<std::input_iterator_tag,
                           typename std::iterator_traits<decltype(range_begin(
                               std::declval<R>()))>::iterator_category>::value
        && std::is_convertible<decltype(*range_begin(std::declval<R>())),
                               Term>::value>> : std::true_type
{
};
#endif

}  // namespace detail

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
  virtual ~AbsSmtSolver() = default;

  /* Sets a solver option with smt-lib 2 syntax
   * SMTLIB: (set-option :<option> <value>)
   * @param option name of the option
   * @param value string value
   */
  virtual void set_opt(const std::string option, const std::string value) = 0;

  /* Sets a solver logic -- see smt-lib 2 logics
   * SMTLIB: (set-logic <logic>)
   * SMT-LIB allows it once, before any declaration, definition, assertion,
   * push or check, and again after reset. Solvers differ on what they
   * accept beyond that: some even after declarations, or more than once.
   * @param logic name of logic
   */
  virtual void set_logic(const std::string logic) = 0;

  /* Add an assertion to the solver
   * SMTLIB: (assert <t>)
   * @param t a boolean term to assert
   */
  virtual void assert_formula(const Term & t) = 0;

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
   * @param assumptions a vector of boolean formulas
   * @return a result object - see result.h
   */
  virtual Result check_sat_assuming(const TermVec & assumptions) = 0;

  /* Check satisfiability under the assumptions in any other range of Terms,
   * such as a TermList or an UnorderedTermSet: anything a range-based for
   * loop accepts, provided its begin and end have the same type. They are
   * copied into a TermVec, so solvers only override the TermVec version.
   * A single Term is iterable over its children but is not a collection of
   * assumptions, so it is rejected: write { t } to assume just t.
   */
  // The constraint depends on the standard the including file is compiled
  // with. Only this inline template differs, and the two forms mangle
  // differently, so code built with either standard links together.
#if defined(__cpp_lib_ranges) && defined(__cpp_concepts)
  template <class Range>
    requires(!std::same_as<Range, Term>)
            && std::ranges::input_range<const Range &>
            && std::ranges::common_range<const Range &>
            && std::convertible_to<
                std::ranges::range_reference_t<const Range &>,
                Term>
#else
  template <
      class Range,
      class = std::enable_if_t<!std::is_same<Range, Term>::value
                               && detail::is_term_range<const Range &>::value>>
#endif
  Result check_sat_assuming(const Range & assumptions)
  {
    // With C++23 this becomes TermVec(std::from_range, assumptions), which
    // also takes ranges whose end is a different sentinel type, and the
    // common-range requirement and the detail helpers can go.
    return check_sat_assuming(TermVec(detail::range_begin(assumptions),
                                      detail::range_end(assumptions)));
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

  /* Apply a sort constructor to sorts
   * SMTLIB: ( <identifier> <sort>+ ), for instance (List Int)
   * Only reachable where the declaration above accepts a nonzero arity,
   * which is the only source of a sort constructor, so this is not pure
   * virtual: the default in solver.cpp throws for the rest.
   * @param sort_con a sort with SortKind UNINTERPRETED_CONS (must have
   * nonzero arity)
   * @param sorts a vector of sorts of size matching sort_con->get_arity()
   * @return a Sort object
   */
  virtual Sort make_sort(const Sort & sort_con, const SortVec & sorts) const;

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
   * @param base the base to interpret the value, for bit-vector sorts (ignored
   * otherwise)
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
