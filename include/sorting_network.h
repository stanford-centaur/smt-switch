/*********************                                                        */
/*! \file sorting_network.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Implements a symbolic sorting network for boolean-sorted variables.
**
**/

#pragma once

#include "smt.h"

namespace smt {

/** \class SortingNetwork
 *         Implements a symbolic sorting network for boolean-sorted variables.
 *         All methods are const so it can be re-used for terms from the same
 *         solver.
 *         Does not return the actual terms, but is used to determine how many
 *         variables are assigned to true symbolically.
 *         Definition:
 *            A sorting network takes a list of boolean terms
 *             and returns a list of the same length.
 *            Let the input be x := [x0, ..., xk]
 *             and let Nt be the number of elements of x that
 *             are set to true in a given model.
 *            Then the output of a sorting network is a list
 *             of boolean terms, y := [y0, ..., yk] such that
 *             yi is true iff Nt >= i
 *            Thus, ignoring the edge cases, Nt = n iff
 *             yn is true and y{n+1} is false
 *
 *         Example:
 *            if the input is [x0, x1, x2, x3]
 *            then the model values for each element in the sorting network
 *            output under any model that 3 of them to true and 1 to false
 *            would be [true, true, true, false]
 */
class SortingNetwork
{
 public:
  SortingNetwork(const SmtSolver & solver) : solver_(solver) {}

  /** Takes a vector of boolean terms
   *  and returns the sorting network output
   *  @param unsorted a vector of boolean terms
   *  @return the (symbolic) sorting network output
   */
  TermVec sorting_network(const TermVec & unsorted) const;

  /** Sorts vectors recursively
   *  Used as helper function for sorting_network
   *  @param unsorted a vector of boolean terms
   *  @param symbolically sorted output
   */
  TermVec sorting_network_rec(const TermVec & unsorted) const;

  /** Return symbolic sorting for two terms
   *  @param t1 the first term
   *  @param t2 the second term
   *  @return a length two vector with the symbolic sorting result
   */
  TermVec sort_two(const Term & t1, const Term & t2) const;

  /** Merges two symbolically sorted vectors
   *  @param sorted1
   *  @param sorted2
   *  @return the combined vector
   */
  TermVec merge(const TermVec & sorted1, const TermVec & sorted2) const;

 protected:
  const SmtSolver & solver_;
};

}  // namespace smt
