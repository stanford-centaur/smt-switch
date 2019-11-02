#ifndef SMT_SOLVER_H
#define SMT_SOLVER_H

#include <string>
#include <vector>

#include "exceptions.h"
#include "result.h"
#include "smt_defs.h"
#include "sort.h"
#include "term.h"

namespace smt {

/**
   Abstract solver class to be implemented by each supported solver.
 */
class AbsSmtSolver
{
 public:
  AbsSmtSolver(){};
  virtual ~AbsSmtSolver(){};

  /* Sets a solver option with smt-lib 2 syntax
   * @param option name of the option
   * @param value string value
   */
  virtual void set_opt(const std::string option, const std::string value) = 0;

  /* Sets a solver logic -- see smt-lib 2 logics
   * @param logic name of logic
   */
  virtual void set_logic(const std::string logic) const = 0;

  /* Add an assertion to the solver
   * @param t a boolean term to assert
   */
  virtual void assert_formula(const Term& t) const = 0;

  /* Check satisfiability of the current assertions
   * @return a result object - see result.h
   */
  virtual Result check_sat() = 0;

  /* Check satisfiability of the current assertions under the given assumptions
   * @param assumptions a vector of boolean literals
   * @return a result object - see result.h
   */
  virtual Result check_sat_assuming(const TermVec & assumptions) = 0;

  /* Push contexts
   * @param num the number of contexts to push
   */
  virtual void push(unsigned int num = 1) = 0;

  /* Pop contexts
   * @param num the number of contexts to pop
   */
  virtual void pop(unsigned int num = 1) = 0;

  /* Get the value of a term after check_sat returns a satisfiable result
   * @param t the term to get the value of
   * @return a value term
   */
  virtual Term get_value(Term& t) const = 0;

  // virtual bool check_sat_assuming() const = 0;

  /* Make an uninterpreted sort
   * @param name the name of the sort
   * @param arity the arity of the sort
   * @return a Sort object
   */
  virtual Sort make_sort(const std::string name,
                         const unsigned int arity) const = 0;

  /* Create a sort
   * @param sk the SortKind (BOOL, INT, REAL)
   * @return a Sort object
   */
  virtual Sort make_sort(const SortKind sk) const = 0;

  /* Create a sort
   * @param sk the SortKind (BV)
   * @return a Sort object
   */
  virtual Sort make_sort(const SortKind sk, const unsigned int size) const = 0;

  /* Create a sort
   * @param sk the SortKind (ARRAY)
   * @return a Sort object
   */
  virtual Sort make_sort(const SortKind sk,
                         const Sort & idxsort,
                         const Sort & elemsort) const = 0;

  /* Create a sort
   * @param sk the SortKind (FUNCTION)
   * @return a Sort object
   */
  virtual Sort make_sort(const SortKind sk,
                         const SortVec & sorts,
                         const Sort & sort) const = 0;

  /* Make a boolean value term
   * @param b boolean value
   * @return a value term with Sort BOOL and value b
   */
  virtual Term make_term(const bool b) const = 0;

  /* Make a bit-vector, int or real value term
   * @param i the value
   * @param sort the sort to create
   * @return a value term with Sort sort and value i
   */
  virtual Term make_term(const int64_t i, const Sort & sort) const = 0;

  /* Make a bit-vector, int, real or (in the future) string value term
   * @param val the numeric value as a string, or a string value
   * @param sort the sort to create
   * @param base the base to interpret the value, for bit-vector sorts (ignored otherwise)
   * @return a value term with Sort sort and value val
   */
  virtual Term make_term(const std::string val,
                         const Sort & sort,
                         unsigned int base = 10) const = 0;

  /* Make a value of a particular sort, such as constant arrays
   * @param op the operator used to create the value (.e.g Const_Array)
   * @param val the Term used to create the value (.e.g constant array with 0)
   * @param sort the sort of value to create
   * @return a value term with Sort sort
   */
  virtual Term make_term(const Term & val, const Sort & sort) const = 0;

  /* Make a symbolic constant or function term
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
   */
  virtual void reset() = 0;

  /* Reset all assertions */
  virtual void reset_assertions() = 0;

  // Methods implemented at the abstract level
  // Note: These can be overloaded in the specific solver implementation for
  //       performance improvements

  /* Substitute all subterms using the provided mapping
   * @param term the term to apply substitution map to
   * @param substitution_map the map to use for substitution
   * @return the term with the substitution map applied
   */
  virtual Term substitute(const Term term,
                          const UnorderedTermMap & substitution_map) const;

  // extra methods -- not required

  /* Dumps full smt-lib representation of current context to a file */
  virtual void dump_smt2(FILE * file) const
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

 protected:
};

}  // namespace smt

#endif
