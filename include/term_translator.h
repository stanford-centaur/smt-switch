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
  Sort transfer_sort(const Sort & sort) const;
  Term transfer_term(const Term & term);
  /* Returns reference to cache -- can be used to populate with symbols */
  UnorderedTermMap & get_cache() { return cache; };

 protected:
  /** Creates a term value from a string of the given sort
   *  @param val the string representation of the value
   *  @param orig_sort the sort from the original solver (transfer_sort is
   * called in this function)
   */
  Term value_from_smt2(const std::string val, const Sort orig_sort) const;
  SmtSolver & solver;
  UnorderedTermMap cache;
};
}  // namespace smt

#endif
