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
  Term value_from_smt2(const std::string val, const Sort sort) const;
  SmtSolver & solver;
  UnorderedTermMap cache;
};
}  // namespace smt

#endif
