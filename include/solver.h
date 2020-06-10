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

#ifndef SMT_SOLVER_H
#define SMT_SOLVER_H

#include <string>
#include <vector>

#include "exceptions.h"
#include "result.h"
#include "smt_defs.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"

namespace smt {

/**
   Abstract solver class to be implemented by each supported solver.
 */
class AbsSmtSolver
{
 public:
  AbsSmtSolver(SolverEnum se) : solver_enum(se){};
  virtual ~AbsSmtSolver(){};

  /* Sets a solver option with smt-lib 2 syntax
   * SMTLIB: (set-option :<option> <value>)
   * @param option name of the option
   * @param value string value
   */
  virtual void set_opt(const std::string option, const std::string value) = 0;

  /* Sets a solver logic -- see smt-lib 2 logics
   * SMTLIB: (set-logic <logic>)
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
   * Note: the assumptions must be boolean literals, not arbitrary formulas
   * SMTLIB: (check-sat-assuming (t1 t2 ... tn)) with asssumptions = [t1,...,tn]
   * @param assumptions a vector of boolean literals
   * @return a result object - see result.h
   */
  virtual Result check_sat_assuming(const TermVec & assumptions) = 0;

  /* Push contexts
   * SMTLIB: (push <num>)
   * @param num the number of contexts to push
   */
  virtual void push(uint64_t num = 1) = 0;

  /* Pop contexts
   * SMTLIB: (pop <num>)
   * @param num the number of contexts to pop
   */
  virtual void pop(uint64_t num = 1) = 0;

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
   *  this function will return a subset of the assumption literals
   *  that are sufficient to make the assertions unsat.
   *  SMTLIB: (get-unsat-assumptions)
   *  @return a vector of assumption literals in the unsat core
   */
  virtual TermVec get_unsat_core() = 0;

  // virtual bool check_sat_assuming() const = 0;

  /* Make an uninterpreted sort
   * SMTLIB: (declare-sort <name> <arity>)
   * @param name the name of the sort
   * @param arity the arity of the sort
   * @return a Sort object
   */
  virtual Sort make_sort(const std::string name, uint64_t arity) const = 0;

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
  virtual Sort make_sort(const SortKind sk, uint64_t size) const = 0;

  /* Create a sort
   * @param sk the SortKind
   * @param sort1 first sort
   * @return a Sort object
   * When sk == ARRAY, sort1 is the index sort and sort2 is the element sort
   */
  virtual Sort make_sort(const SortKind sk, const Sort & sort1) const = 0;

  /* Create a sort
   * @param sk the SortKind
   * @param sort1 first sort
   * @param sort2 second sort
   * @return a Sort object
   * When sk == ARRAY, sort1 is the index sort and sort2 is the element sort
   */
  virtual Sort make_sort(const SortKind sk,
                         const Sort & sort1,
                         const Sort & sort2) const = 0;

  /* Create a sort
   * @param sk the SortKind
   * @param sort1 first sort
   * @param sort2 second sort
   * @param sort3 third sort
   * @return a Sort object
   */
  virtual Sort make_sort(const SortKind sk,
                         const Sort & sort1,
                         const Sort & sort2,
                         const Sort & sort3) const = 0;

  /* Create a sort
   * @param sk the SortKind (FUNCTION)
   * @param sorts a vector of sorts (for function SortKind, last sort is return
   * type)
   * @return a Sort object
   * Note: This is the only way to make a function sort
   */
  virtual Sort make_sort(const SortKind sk, const SortVec & sorts) const = 0;

  /* Create a datatype sort
   * @param d the Datatype Declaration
   * @return a Sort object
   */
  virtual Sort make_sort(const DatatypeDecl & d) const = 0;

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
  virtual Term make_term(int64_t i, const Sort & sort) const = 0;

  /* Make a bit-vector, int, real or (in the future) string value term
   * @param val the numeric value as a string, or a string value
   * @param sort the sort to create
   * @param base the base to interpret the value, for bit-vector sorts (ignored otherwise)
   * @return a value term with Sort sort and value val
   */
  virtual Term make_term(const std::string val,
                         const Sort & sort,
                         uint64_t base = 10) const = 0;

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

  /* Make a new term
   * @param op the operator to use
   * @param t the child term
   * @return the created term
   */
  virtual Term make_term(const Op op, const Term & t) const = 0;

  /* Make a new term
   * @param op the operator to use
   * @param t0 the first child term
   * @param t1 the second child term
   * @return the created term
   */
  virtual Term make_term(const Op op,
                         const Term & t0,
                         const Term & t1) const = 0;

  /* Make a new term
   * @param op the operator to use
   * @param t0 the first child term
   * @param t1 the second child term
   * @param t2 the third child term
   * @return the created term
   */
  virtual Term make_term(const Op op,
                         const Term & t0,
                         const Term & t1,
                         const Term & t2) const = 0;

  /* Make a new term
   * @param op the operator to use
   * @param terms vector of children
   * @return the created term
   */
  virtual Term make_term(const Op op, const TermVec & terms) const = 0;

  /* Return the solver to it's startup state
   * WARNING: This destroys all created terms and sorts
   * SMTLIB: (reset)
   */
  virtual void reset() = 0;

  /* Reset all assertions 
   * SMTLIB: (reset-assertions)
   */
  virtual void reset_assertions() = 0;


  /* Initialize a datatype declaration with some name
   * @param s Name of the datatype
   * @return an empty Datatype declaration
   */
  virtual DatatypeDecl make_datatype_decl(const std::string & s) = 0;

  /* Initialize a datatype constructor declaration with some name
   * @param s Name of the datatype constructor
   * @return an empty Datatype declaration
   */
  virtual DatatypeConstructorDecl make_datatype_constructor_decl(const std::string s) const = 0; // what is const=0?

  /* Add a datatype constructor to a datatype declaration
   * @param dt Datatype
   * @param con Datatype constructor
   */
 virtual void add_constructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const = 0; // what is const=0?

  /* Add a selector to a datatype constructor
   * @param dt DatatypeConstructorDecl
   * @param name name of the selector
   * @param s sort of the selector
   */

  virtual void add_selector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const = 0;

  /* Add a selector to a datatype constructor where the sort is the datatype itself (whose sort doesn't exist yet)
   * @param dt DatatypeConstructorDecl
   * @param name name of the selector
   */
  virtual void add_selector_self(DatatypeConstructorDecl & dt, const std::string & name) const = 0;

  /* get a term representing to a datatype constructor
   * @param s A datatype sort (error otherwise)
   * @param name name of the constructor
   */

  virtual Term get_constructor(const Sort & s, std::string name) const = 0;

  /* get a term representing to a datatype tester
   * @param s A datatype sort (error otherwise)
   * @param name name of the constructor
   */

  virtual Term get_tester(const Sort & s, std::string name) const = 0;

  /* get a term representing to a datatype selector
   * @param s A datatype sort (error otherwise)
   * @param con name of the constructor
   * @param name name of the selector
   */
  virtual Term get_selector(const Sort & s, std::string con, std::string name) const = 0;


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

  // extra methods -- not required

  /* Dumps full smt-lib representation of current context to a file */
  virtual void dump_smt2(std::string filename) const
  {
    throw NotImplementedException("Dumping to FILE not supported for this solver.");
  }

  /* Compute a Craig interpolant given A and B such that A ^ B is unsat
   *   i.e. an I such that: A -> I  and  I ^ B is unsat
   *        and I only contains constants that are in both A and B
   * @param A the A term for a craig interpolant
   * @param B the B term for a craig interpolant
   * @param out_I the term to store the computed interpolant in
   * @return true iff an interpolant was computed
   *
   * Throws an SmtException if the formula was actually sat or
   *   if computing the interpolant failed.
   */
  virtual bool get_interpolant(const Term & A,
                               const Term & B,
                               Term & out_I) const
  {
    throw NotImplementedException("Interpolants are not supported by this solver.");
  }

  SolverEnum get_solver_enum() { return solver_enum; };

 protected:
  SolverEnum solver_enum;  ///< an enum identifying the underlying solver
};

}  // namespace smt

#endif
