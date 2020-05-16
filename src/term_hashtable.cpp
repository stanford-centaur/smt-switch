#include "term_hashtable.h"

using namespace std;

namespace smt {

/* TermHashTable */

TermHashTable::TermHashTable() {}

TermHashTable::~TermHashTable() {}

void TermHashTable::insert(const Term & t) { table[t->hash()].insert(t); }

bool TermHashTable::lookup(Term & t)
{
  size_t hashval = t->hash();
  if (table.find(hashval) != table.end()
      && table[hashval].find(t) != table[hashval].end())
  {
    // reassign t
    // should destroy the previous Term
    // when reference counter goes to zero
    t = *(table[hashval].find(t));
    return true;
  }
  return false;
}

void TermHashTable::erase(const Term & t)
{
  size_t hashval = t->hash();
  if (table.find(hashval) != table.end()
      && table[hashval].find(t) != table[hashval].end())
  {
    table[hashval].erase(t);
  }
}

void TermHashTable::clear() { table.clear(); }

}  // namespace smt
