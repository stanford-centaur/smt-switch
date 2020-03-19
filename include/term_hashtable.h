#pragma once

#include <unordered_map>

#include "smt_defs.h"
#include "term.h"

namespace smt {

/** \class TermHashTable
 *  A very straightforward implementation of a Term hash table
 *  using a std::unordered_map and UnorderedTermSet
 *  The primary use of this is for hash-consing in LoggingSolver
 */
class TermHashTable
{
 public:
  TermHashTable();
  ~TermHashTable();
  void insert(const Term & t);
  bool lookup(Term t);
  void erase(const Term & t);

 protected:
  std::unordered_map<std::size_t, UnorderedTermSet> table;
};

}  // namespace smt
