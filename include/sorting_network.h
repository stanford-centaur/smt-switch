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
** \brief Implements a symbolic sorting network for boolean-sorted terms.
**
**/

#pragma once

#include "smt.h"

namespace smt {

/** \class SortingNetwork
 *         Implements a symbolic sorting network for boolean-sorted terms.
 *         All methods are const so it can be re-used for terms from the same
 *          solver.
 *         Returns a vector of new terms, which can be used to determine how
 *          many terms are assigned to true symbolically.
 *         Definition:
 *            A sorting network takes a list of boolean terms
 *             and returns a list of the same length.
 *            Let the input be x := [x0, ..., xk],
 *             then the output of a sorting network is a list
 *             of boolean terms, y := [y0, ..., yk] such that
 *             any model assigns yi to true iff i or more
 *             elements of x were set to true in that model.
 *            Let Nt be the number of elements of x set to
 *             true in a given model.
 *            Ignoring the edge cases, in a given model, Nt = n iff
 *             yn is true and y{n+1} is false
 *            The edge case is at Nt = k, since there is no y{k+1}
 *             In this case, yk is true iff Nt = k
 *
 *         Example 1:
 *            if the input is [x0, x1]
 *            the output is [Or(x0, x1), And(x0, x1)]
 *            so that the first term evaluates to true iff one or more
 *            of the inputs evaluates to true, and the second evaluates
 *            to true iff both evaluate to true
 *         Example 2:
 *            if the input is [x0, x1, x2, x3]
 *             then the model values for each element in the sorting network
 *             output for any model that sets 3 of them to true and 1 to false
 *             would be [true, true, true, false].
 *            Note that these are the model values, not the terms that will
 *             be returned from the function.
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

  /** Return symbolic sorting for two terms
   *  Used as helper in sorting_network_rec and merge
   *  @param t1 the first term
   *  @param t2 the second term
   *  @return a length two vector with the symbolic sorting result
   */
  TermVec sort_two(const Term & t1, const Term & t2) const;

  /** Merges two symbolically sorted vectors
   *  Used as helper in sorting_network_rec
   *  @param sorted1
   *  @param sorted2
   *  @return the combined vector
   */
  TermVec merge(const TermVec & sorted1, const TermVec & sorted2) const;

 protected:
  const SmtSolver & solver_;

  /** Sorts vectors recursively
   *  Used as helper function for sorting_network
   *  @param unsorted a vector of boolean terms
   *  @param symbolically sorted output
   */
  TermVec sorting_network_rec(const TermVec & unsorted) const;

};

}  // namespace smt
