/*!
 * \file term_hashtable.cpp
 * \brief A simple hash table of terms, used for hash-consing in LoggingSolver
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/term_hashtable.h"

#include <cstddef>
#include <unordered_set>

namespace smt {

/* TermHashTable */

void TermHashTable::insert(const Term & t) { table[t->hash()].insert(t); }

bool TermHashTable::contains(const Term & t) const
{
  std::size_t hashval = t->hash();
  return (table.find(hashval) != table.end()
          && table.at(hashval).find(t) != table.at(hashval).end());
}

bool TermHashTable::lookup(Term & t) const
{
  if (contains(t))
  {
    // reassign t
    // should destroy the previous Term
    // when reference counter goes to zero
    t = *(table.at(t->hash()).find(t));
    return true;
  }
  return false;
}

void TermHashTable::erase(const Term & t)
{
  std::size_t hashval = t->hash();
  if (table.find(hashval) != table.end()
      && table[hashval].find(t) != table[hashval].end())
  {
    table[hashval].erase(t);
  }
}

void TermHashTable::clear() { table.clear(); }

}  // namespace smt
