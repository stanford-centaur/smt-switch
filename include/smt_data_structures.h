#ifndef SMT_DATA_STRUCTURES_H
#define SMT_DATA_STRUCTURES_H

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "term.h"
#include "sort.h"

namespace smt {

struct TermHashFunction
{
  std::size_t operator()(const Term & t) const
  {
    // call the term's hash function, implemented by solvers
    return t->hash();
  }
};

using TermVec = std::vector<Term>;
using UnorderedTermSet = std::unordered_set<Term, TermHashFunction>;
using UnorderedTermMap = std::unordered_map<Term, Term, TermHashFunction>;

// range-based iteration
inline TermIter begin(Term & t) { return t->begin(); }
inline TermIter end(Term & t) { return t->end(); }

struct SortHashFunction
{
  std::size_t operator()(const Sort & s) const
  {
    // call the sort's hash function, implemented by solvers
    return s->hash();
  }
};

 using SortVec = std::vector<Sort>;
 using UnorderedSortSet = std::unordered_set<Sort, SortHashFunction>;

}  // namespace smt

#endif
