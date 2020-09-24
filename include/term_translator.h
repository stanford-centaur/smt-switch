/*********************                                                        */
/*! \file term_translator.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class for translating terms from one solver to another. Keeps
**        a cache so it can be called multiple times (without redeclaring
**        symbols, which would throw an exception).
**/

#pragma once

#include <unordered_map>

#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"

namespace smt {

/** Class for translating terms from *one* other solver to *one* new solver
 *  will fail if you try to convert terms from more than one solver
 *  e.g.
 *  SmtSolver s1 = CVC4SolverFactory::create(false);
 *  SmtSolver s2 = MsatSolverFactory::create(false);
 *  SmtSolver s3 = CVC4SolverFactory::create(false);
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
 *  // if s2 were also a CVC4Solver, it depends on how the underlying solver
 *  // handles terms from different instances. In the case of CVC4, it will
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
  TermTranslator(const SmtSolver & s) : solver(s) {}
  /** Transfers a sort from the other solver to this solver
   *  @param the sort transfer
   *  @return a sort belonging to this solver
   */
  Sort transfer_sort(const Sort & sort);

  /** Transfers a term from the other solver to this solver
   *  @param term the term to transfer to the member variable solver
   *  @return a term belonging to this solver
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
  UnorderedTermMap & get_cache() { return cache; };

  /* Returns a reference to the solver this object translates terms to */
  const SmtSolver & get_solver() { return solver; };

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
   * @param smtlib is the smtlib representation
   * @return the infix-style representation
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

  // Note: const meaning the solver doesn't change to a different solver
  // it can still call non-const methods of the solver
  SmtSolver solver;  ///< solver to translate terms to
  UnorderedTermMap cache;
  // map from uninterpreted sort names to the sort in the destination solver
  // necessary because it needs to be the same exact uninterpreted sort
  // cannot recreate it with the same name and get the same object back
  std::unordered_map<std::string, Sort> uninterpreted_sorts;
};
}  // namespace smt

