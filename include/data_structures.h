#ifndef SMT_DATA_STRUCTURES_H
#define SMT_DATA_STRUCTURES_H

#include <unordered_map>
#include <vector>

#include "term.h"

namespace smt {
using TermVec = std::vector<Term>;

struct TermHashFunction
{
  std::size_t operator()(const Term& t) const
  {
    // call the term's hash function, implemented by solvers
    return t->hash();
  }
};

using TermUnorderedMap = std::unordered_map<Term, Term, TermHashFunction>;
}  // namespace smt

#endif
