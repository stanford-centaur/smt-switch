#ifndef SMT_SOLVER_H
#define SMT_SOLVER_H

#include <string>
#include <vector>

#include "result.h"
#include "smt_data_structures.h"
#include "smt_defs.h"
#include "sort.h"

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
   * @param value boolean value
   */
  virtual void set_opt(const std::string option, const bool value) const = 0;
  /* Sets a solver option with smt-lib 2 syntax
   * @param option name of the option
   * @param value string value
   */
  virtual void set_opt(const std::string option,
                       const std::string value) const = 0;

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
  virtual Result check_sat() const = 0;

  /* Check satisfiability of the current assertions under the given assumptions
   * @param assumptions a vector of boolean assumption terms
   * @return a result object - see result.h
   */
  virtual Result check_sat_assuming(const TermVec & assumptions) const = 0;

  /* Push contexts
   * @param num the number of contexts to push
   */
  virtual void push(unsigned int num = 1) const = 0;

  /* Pop contexts
   * @param num the number of contexts to pop
   */
  virtual void pop(unsigned int num = 1) const = 0;

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
                         const Sort idxsort,
                         const Sort elemsort) const = 0;

  /* Create a sort
   * @param sk the SortKind (FUNCTION)
   * @return a Sort object
   */
  virtual Sort make_sort(const SortKind sk,
                         const std::vector<Sort> sorts,
                         const Sort sort) const = 0;

  /* Make a boolean value term
   * @param b boolean value
   * @return a value term with Sort BOOL and value b
   */
  virtual Term make_value(const bool b) const = 0;

  /* Make a bit-vector, int or real value term
   * @param i the value
   * @param sort the sort to create
   * @return a value term with Sort sort and value i
   */
  virtual Term make_value(const unsigned int i, const Sort sort) const = 0;

  /* Make a bit-vector, int, real or (in the future) string value term
   * @param val the numeric value as a string, or a string value
   * @param sort the sort to create
   * @param base the base to interpret the value, for bit-vector sorts (ignored otherwise)
   * @return a value term with Sort sort and value val
   */
  virtual Term make_value(const std::string val, const Sort sort, unsigned int base = 10) const = 0;

  /* Make a symbolic constant or function term
   * @param name the name of constant or function
   * @param sort the sort of this constant or function
   * @return the symbolic constant or function term
   */
  virtual Term make_term(const std::string name, const Sort sort) = 0;

  /* Make a new term
   * @param op the operator to use
   * @param t the child term
   * @return the created term
   */
  virtual Term make_term(const Op op, const Term t) const = 0;

  /* Make a new term
   * @param op the operator to use
   * @param t0 the first child term
   * @param t1 the second child term
   * @return the created term
   */
  virtual Term make_term(const Op op, const Term t0, const Term t1) const = 0;

  /* Make a new term
   * @param op the operator to use
   * @param t0 the first child term
   * @param t1 the second child term
   * @param t2 the third child term
   * @return the created term
   */
  virtual Term make_term(const Op op,
                         const Term t0,
                         const Term t1,
                         const Term t2) const = 0;

  /* Make a new term
   * @param op the operator to use
   * @param terms vector of children
   * @return the created term
   */
  virtual Term make_term(const Op op, const std::vector<Term> terms) const = 0;

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

  /* Transfer a sort from some other solver to this solver
   *    Warning: does not check if the term already belongs to this solver
   * @param the sort to transfer
   * @return the transferred sort
   */
  virtual Sort transfer_sort(const Sort sort);

  /* Transfer a term from some other solver to this solver
   *    Warning: does not check if the term already belongs to this solver
   * @param the term to transfer
   * @return the transferred term
   */
  virtual Term transfer_term(const Term term);

  /* Takes a smt-lib2 value term and creates a Term
   * @param val value term in smt2 format
   * @param sort how to interpret the value (e.g. Real vs Int)
   */
  virtual Term value_from_smt2(const std::string val, const Sort sort) const;

 protected:
  // IMPORTANT: new symbols should be registered here
  //            this is the responsibility of the solver implementation
  // Note: has to be on heap or get strange errors
  std::unordered_map<std::string, Term> * symbols =
      new std::unordered_map<std::string, Term>();
};

}  // namespace smt

#endif
