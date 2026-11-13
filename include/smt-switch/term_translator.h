/*!
 * \file term_translator.h
 * \brief Class for translating terms from one solver to another
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * It keeps a cache, so it can be called several times without redeclaring
 * symbols, which would throw an exception.
 */
#ifndef SMT_SWITCH_TERM_TRANSLATOR_H
#define SMT_SWITCH_TERM_TRANSLATOR_H

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {

/** Class for translating terms from *one* other solver to *one* new solver
 *  will fail if you try to convert terms from more than one solver
 *  e.g.
 *  SmtSolver s1 = Cvc5SolverFactory::create(false);
 *  SmtSolver s2 = MsatSolverFactory::create(false);
 *  SmtSolver s3 = Cvc5SolverFactory::create(false);
 *
 *  Term x = s1->make_symbol("x", s1->make_sort(INT));
 *  Term y = s2->make_symbol("y", s2->make_sort(INT));
 *
 *  TermTranslator to_s3(s3);
 *  Term x3 = to_s3.transfer_term(x);
 *  // This line would segfault
 *  Term y3 = to_s3.transfer_term(y);
 *  // this is because the cache will already have x, a Term from s1 in it
 *  // and then transferring y from s2 will trigger a comparison between x
 *  // and y. But these are terms from two different solvers and the static
 *  // pointer cast will be an incorrect cast.
 *  // if s2 were also a Cvc5Solver, it depends on how the underlying solver
 *  // handles terms from different instances. In the case of cvc5, it will
 *  // throw an exception
 *
 *  This class has no reference to the other solver because it's not needed
 *  it only needs the solver that's being transferred *to* so that it can
 *  make sorts and terms.
 *  Because symbols can only be declared once, there will be errors
 *  if the symbol is already declared in the new solver. To avoid this
 *  populate the TermTranslator's cache with a mapping from
 *  <other solver's symbol> -> <new solver's symbol>
 */
class TermTranslator
{
 public:
  /** @param s the solver or interpolator to translate terms to */
  explicit TermTranslator(const SmtTermBuilder & s);
  /** Transfers a sort from the other solver to this solver
   *  @param the sort transfer
   *  @return a sort belonging to this solver
   */
  Sort transfer_sort(const Sort & sort);

  /** Transfers a term from the other solver to this solver
   *  @param term the term to transfer to the member variable solver
   *  @return a term belonging to this solver
   *  @throws IncorrectUsageException if this solver already has a symbol of
   *          the term's name with a sort it cannot be cast to, or a function
   *          is applied to more or fewer arguments than its new sort takes
   *  @throws NotImplementedException for a term that is not a symbol,
   *          param, value or operator application
   */
  Term transfer_term(const Term & term);

  /** Transfers a term and casts it to a particular SortKind
   *  for now, only supports Bool <-> BV1 and Int <-> Real
   *  will throw an exception if something else is requested
   *  @param term the term to transfer to the member variable solver
   *  @param sk the expected SortKind of the transferred term
   *  @return a term belonging to this solver
   */
  Term transfer_term(const Term & term, const SortKind sk);

  /* Returns reference to cache -- can be used to populate with symbols */
  UnorderedTermMap & get_cache();

  /* Returns a reference to the solver or interpolator this object translates
   * terms to */
  const SmtTermBuilder & get_term_builder() const;

  /* Returns the solver this object translates terms to
   * @throws IncorrectUsageException if it translates them to an interpolator
   */
  [[deprecated("use get_term_builder")]] SmtSolver get_solver() const;

 protected:
  /** Creates a term value from a string of the given sort
   *  @param val the string representation of the value
   *  @param orig_sort the sort from the original solver (transfer_sort is
   *  called in this function)
   *  @return a term with the given value
   */
  Term value_from_smt2(const std::string val, const Sort sort);

  /** translates an smtlib representation of a const rational "(/ a b)"
   *  into a infix-style representation of a const rational "a / b"
   *  A numerator or denominator written as an integral decimal ("1.0")
   *  loses its point. A string that is not an s-expression, such as an
   *  infix "a/b", is returned unchanged.
   * @param smtlib is the smtlib representation
   * @return the infix-style representation
   * @throws IncorrectUsageException if smtlib is a malformed fraction
   */
  std::string infixize_rational(const std::string smtlib) const;

  /** identifies relevant casts to perform an operation
   *  assumes the operation is currently not well-sorted
   *  e.g. check_sortedness returns false
   *  could be more general in the future, for now focusing on
   *  Bool / BV1 case
   *  It can either change the operator or cast the terms
   *  @param op the operator that should be applied
   *  @param terms the terms to apply it to
   *  @return a well-sorted term with an operator applied to casted terms
   *  Note: the operator can change, e.g. BVAnd -> And
   *  This method uses cast_term
   */
  Term cast_op(Op op, const TermVec & terms) const;

  /** casts a term to a different sort
   *  could be more general in future, for now just does a few common
   * conversions such as: Bool <-> BV1 Int  <-> Real
   *  @param term the term to cast
   *  @param the sort to cast it to
   *  @return the new term
   *  throws a NotImplementedException if it cannot interpret the cast
   *  the term and sort MUST belong to the same solver
   */
  Term cast_term(const Term & term, const Sort & sort) const;

  /** casts a value term to a different sort
   *  could be more general in future, for now just does
   * conversions such as: Bool <-> BV1
   *  @param val the value term to cast
   *  @param the sort to cast it to
   *  @return the new term
   *  throws a NotImplementedException if it cannot interpret the cast
   *  the term and sort MUST belong to the same solver
   */
  Term cast_value(const Term & term, const Sort & sort) const;

  /** widens the Int terms among terms that also hold a Real
   *  @param terms the terms, which are widened in place
   */
  void widen_ints(TermVec & terms) const;

  /** The uninterpreted sort or sort constructor of this name in the
   *  member variable solver, declared on first use
   *  @param name the name of the sort
   *  @param arity the arity of the sort, zero for an uninterpreted sort
   *  @return the sort, the same object for every call with this name
   *  throws an IncorrectUsageException if the name was declared with a
   *  different arity
   */
  Sort uninterpreted_sort(const std::string & name, std::uint64_t arity);

  /** Declares a datatype in the member variable solver as the other solver
   *  declared it, transferring the sorts of its selectors
   *  @param sort a datatype sort of the other solver
   *  @return the datatype sort of this name in the member variable solver,
   *  the same object for every call with this name
   *  throws a NotImplementedException for a datatype that another datatype
   *  among its selectors' sorts refers back to
   */
  Sort transfer_datatype_sort(const Sort & sort);

  /** The constructor, selector or tester of the member variable solver
   *  that matches one of the other solver, found by its printed name
   *  @param term a constructor, selector or tester of the other solver
   *  @return the same component of the transferred datatype
   *  throws an SmtException if term prints as none of its datatype's
   *  constructors, selectors or testers
   */
  Term transfer_datatype_component(const Term & term);

  SmtTermBuilder builder;  ///< solver or interpolator to translate terms to
  UnorderedTermMap cache = {};
  // map from uninterpreted sort names to the sort in the destination solver
  // necessary because it needs to be the same exact uninterpreted sort
  // cannot recreate it with the same name and get the same object back
  std::unordered_map<std::string, Sort> uninterpreted_sorts = {};
  // map from datatype names to the sort in the destination solver, which
  // like an uninterpreted sort cannot be declared twice and stay the same
  std::unordered_map<std::string, Sort> datatype_sorts = {};
  // the datatypes whose transfer has begun and not yet finished
  std::unordered_set<std::string> datatypes_in_progress = {};
};
}  // namespace smt

#endif  // SMT_SWITCH_TERM_TRANSLATOR_H
