/*!
 * \file term_hashtable.h
 * \brief A simple hash table of terms, used for hash-consing in LoggingSolver
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_TERM_HASHTABLE_H
#define SMT_SWITCH_TERM_HASHTABLE_H

#include <cstddef>
#include <unordered_map>

#include "smt-switch/smt_defs.h"
#include "smt-switch/term.h"

namespace smt {

/** \class TermHashTable
 *  A very straightforward implementation of a Term hash table
 *  using a std::unordered_map and UnorderedTermSet
 *  The primary use of this is for hash-consing in LoggingSolver
 */
class TermHashTable
{
 public:
  void insert(const Term & t);
  /** check if a term is in the table
   *  @param the term to check
   *  @return true iff the term is already in the table
   */
  bool contains(const Term & t) const;
  /** lookup a term and modify pointer in place
   *  @param t the term to look up and modify
   *  @return true iff the term was found in the hash table
   */
  bool lookup(Term & t) const;
  void erase(const Term & t);
  void clear();

 protected:
  std::unordered_map<std::size_t, UnorderedTermSet> table = {};
};

}  // namespace smt

#endif  // SMT_SWITCH_TERM_HASHTABLE_H
