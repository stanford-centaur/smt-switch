/*********************                                                        */
/*! \file term_hashtable.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief A simple hash table for terms -- used for hash-consing in
** LoggingSolver
**
**
**/

#pragma once

#include <cstddef>
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
  /** check if a term is in the table
   *  @param the term to check
   *  @return true iff the term is already in the table
   */
  bool contains(const Term & t) const;
  /** lookup a term and modify pointer in place
   *  @param t the term to look up and modify
   *  @return true iff the term was found in the hash table
   */
  bool lookup(Term & t);
  void erase(const Term & t);
  void clear();

 protected:
  std::unordered_map<std::size_t, UnorderedTermSet> table;
};

}  // namespace smt
