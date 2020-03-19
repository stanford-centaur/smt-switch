#include "term_hashtable.h"

using namespace std;

namespace smt {

/* TermHashTable */

TermHashTable::TermHashTable() {}

TermHashTable::~TermHashTable() {}

void TermHashTable::insert(const Term & t) { table[t->hash()].insert(t); }

bool lookup(Term t)
{
  size_t hashval = t->hash();
  if (table.find(hashval) != table.end()
      && table[hashval].find(t) != table[hashval].end())
  {
    // reassign t
    // should destroy the previous Term
    // when reference counter goes to zero
    t = table[hashval].at() return true;
  }
  return false;
}

void erase(const Term & t)
{
  size_t hashval = t->hash();
  if (table.find(hashval) != table.end()
      && table[hashval].find(t) != table[hashval].end())
  {
    table[hashval].erase(t);
  }
}

}  // namespace smt
