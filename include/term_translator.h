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

#ifndef SMT_TERM_TRANSLATOR_H
#define SMT_TERM_TRANSLATOR_H

#include <unordered_map>

#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"

namespace smt {
class TermTranslator
{
 public:
  TermTranslator(SmtSolver & s) : solver(s) {}
  Sort transfer_sort(const Sort & sort);
  Term transfer_term(const Term & term);
  /* Returns reference to cache -- can be used to populate with symbols */
  UnorderedTermMap & get_cache() { return cache; };

 protected:
  /** interprets a string as a SMT value
   *  @param val the string value in SMT-LIB2 format
   *  @param the sort of the value
   *  @return a term with that value
   */
  Term value_from_smt2(const std::string val, const Sort sort) const;

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
  SmtSolver & solver;
  UnorderedTermMap cache;
};
}  // namespace smt

#endif
