/*********************                                                        */
/*! \file sort_inference.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Utility functions for checking sortedness and computing the
**        expected sort when building a term.
**
**/

#include <initializer_list>

#include "ops.h"
#include "sort.h"

namespace smt {

// useful helper functions -- used for sort checking

/** Checks that the sorts are equivalent
 *  @param sorts a non-empty vector of sorts
 *  @return true iff they're all equal
 */
bool is_sort_equal(const SortVec & sorts);

/** Checks that the sorts have the same SortKind
 *  @param sorts a non-empty vector of sorts
 *  @return true iff they're all equal
 */
bool is_sortkind_equal(const SortVec & sorts);
}  // namespace smt
