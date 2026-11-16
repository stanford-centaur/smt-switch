/*!
 * \file disjoint_set.h
 * \brief Disjoint sets of terms
 * \author Ahmed Irfan
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_DISJOINT_SET_H
#define SMT_SWITCH_DISJOINT_SET_H

#include <unordered_map>

#include "smt-switch/smt_defs.h"

namespace smt {

/** A generic implementation of Disjoint Sets for smt-switch terms.
 *  Supports a comparator for ranking of terms.
 */
class DisjointSet
{
 public:
  explicit DisjointSet(bool (*c)(const Term & a, const Term & b));

  /** Add two terms a and b in the same set.
   * @param Term a to be added in the same set
   * @param Term b to be added in the same set
   */
  void add(const Term & a, const Term & b);

  /** Find the representative (leader) of the term t.
   * @param Term t whose respresentative to be returned.
   * returns the representative term.
   * @throws IncorrectUsageException if t was never added
   */
  Term find(const Term & t) const;

  /** Clears the disjoint set
   */
  void clear();

 private:
  // Compare function for ranking
  bool (*comp)(const Term & a, const Term & b);

  // member to group's leader
  UnorderedTermMap leader_ = {};
  // group leader to group
  std::unordered_map<Term, UnorderedTermSet> group_ = {};
};

}  // namespace smt

#endif  // SMT_SWITCH_DISJOINT_SET_H
