/*********************                                                        */
/*! \file utils.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Ahmed Irfan
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Utility functions.
**
**
**/

#pragma once

#include <iostream>
#include "assert.h"
#include <string>
#include "smt.h"

#ifndef NDEBUG
#define _ASSERTIONS
#endif

#if !defined(NDEBUG) || defined(_ASSERTIONS)
#define Assert(EX) (void)((EX) || (__assert(#EX, __FILE__, __LINE__), 0))
#define Unreachable() \
  (void)((__assert("location should be unreachable", __FILE__, __LINE__), 0))
#else
#define Assert(EX)
#define Unreachable()
#endif

#ifdef _LOGGING_LEVEL
const std::size_t global_log_level = _LOGGING_LEVEL;
#else
const std::size_t global_log_level = 0;
#endif

// logs to stdout
template <std::size_t lvl>
inline void Log(std::string msg)
{
  if (global_log_level >= lvl)
  {
    std::cout << msg << std::endl;
  }
}

namespace smt {

// term helper methods
void op_partition(smt::PrimOp o, const smt::Term & term, smt::TermVec & out);

/** Populates a vector with conjuncts from a term
 *  @param the term to partition
 *  @param out the output vector
 *  @param include_bvand also split on BVAnd over 1-bit signals
 *         Note: this is mainly for use with Boolector which treats
 *         booleans as 1-bit bit-vectors. Using this option on a term
 *         that is known to be boolean will give you the expected
 *         partition.
 */
void conjunctive_partition(const smt::Term & term,
                           smt::TermVec & out,
                           bool include_bvand = false);

/** Populates a vector with disjuncts from a term
 *  @param the term to partition
 *  @param out the output vector
 *  @param include_bvor also split on BVOr over 1-bit signals
 */
void disjunctive_partition(const smt::Term & term,
                           smt::TermVec & out,
                           bool include_bvor = false);

void get_matching_terms(const smt::Term & term,
                        smt::UnorderedTermSet & out,
                        bool (*matching_fun)(const smt::Term & term));

void get_free_symbolic_consts(const smt::Term & term,
                              smt::UnorderedTermSet & out);

void get_free_symbols(const smt::Term & term, smt::UnorderedTermSet & out);

void get_ops(const smt::Term & term, smt::UnorderedOpSet & out);

/** returns true iff l is a literal
 *  e.g. either a boolean symbolic constant or its negation
 *  NOTE will return false for nested negations, i.e. (not (not (not l)))
 *  @param l the term to check
 *  @param boolsort a boolean sort from the corresponding solver
 *         this way sort aliasing solvers are still supported
 *  @return true iff l is a literal
 */
bool is_lit(const Term & l, const Sort & boolsort);


std::string cnf_to_dimacs(Term cnf);

//Returns a string in DIMACs format for a given cnf formula

// -----------------------------------------------------------------------------

/** \class
 * UnsatcoreReducer class.
 * Implements an interative unsatcore reducer procedure. 
 *
 * reducer_solver is the solver that will be used for unsatcore extraction in
 * the procedure. It is different from the ext_solver (external solver used to
 * create the formula and assump)
 *
 */
class UnsatCoreReducer {
public:
  UnsatCoreReducer(smt::SmtSolver reducer_solver);
  ~UnsatCoreReducer();

  /** The main method to reduce the assump (vector of assumptions). The method
   *  assumes that the conjunction of the formula and assump is unsatisfiable.
   *  @param input formula
   *  @param input vector of assumptions
   *  @param output vector for the reduced assumptions
   *  @param output vector for the removed assumptions
   *  @param iter is the number of iterations done in the method. Default is 0,
   *         and it means that the result in out_red will be minimal.
   *  @param rand_seed if strickly positive then assump will be shuffled.
   *  returns false if the formula conjoined with the assump is satisfiable,
   *          otherwise returns true
   */
  bool reduce_assump_unsatcore(const smt::Term &formula,
                               const smt::TermVec &assump,
                               smt::TermVec &out_red,
                               smt::TermVec *out_rem = NULL,
                               unsigned iter = 0,
                               unsigned rand_seed = 0);
  

  /** The additional method to reduce the assump (vector of assumptions). The method
   *  assumes that the conjunction of the formula and assump is unsatisfiable.
   *  This will iterate through the assump and requires at most size(assump) query
   *  Note: this function assumes that there are no duplicate assumptions from the
   *  second input vector.
   *  @param input formula
   *  @param input vector of assumptions
   *  @param output vector for the reduced assumptions
   *  @param output vector for the removed assumptions
   *  @param iter is the number of iterations done in the method. Default is 0,
   *         and it means that the result in out_red will be minimal.
   *  returns false if the formula conjoined with the assump is satisfiable,
   *          otherwise returns true
   */
  bool linear_reduce_assump_unsatcore(
                               const smt::Term &formula,
                               const smt::TermVec &assump,
                               smt::TermVec &out_red,
                               smt::TermVec *out_rem = NULL,
                               unsigned iter = 0);

  /** This clears the term translation cache. Note, term translator is used to
   *  translate the terms of the external solver to the
   *  unsat-assumption-reducer-solver. A use-case of this method is to call it
   * before calling the reduce_assump_unsat from one call to another call when
   * the external solver in the first call is different from the second call.
   */
  void clear_term_translation_cache() { to_reducer_.get_cache().clear(); };

 private:
  /** returns a label that will be used to precondition the assumption term 't'
   *  @param Input term t
   *  return a boolean label for the term t
   */
  smt::Term label(const Term & t);

  smt::SmtSolver reducer_; // solver for unsatcore-based reduction
  smt::TermTranslator to_reducer_; // translator for converting terms from
                                   // ext_solver to reducer_

  smt::UnorderedTermMap labels_;  //< labels for unsat cores
};

// -----------------------------------------------------------------------------

/** A generic implementation of Disjoint Sets for smt-switch terms.
 *  Supports a comparator for ranking of terms.
 */
class DisjointSet
{
 public:
  DisjointSet(bool (*c)(const smt::Term & a, const smt::Term & b));
  ~DisjointSet();

  DisjointSet() = delete;

  /** Add two terms a and b in the same set.
   * @param Term a to be added in the same set
   * @param Term b to be added in the same set
   */
  void add(const smt::Term & a, const smt::Term & b);

  /** Find the representative (leader) of the term t.
   * @param Term t whose respresentative to be returned.
   * returns the representative term.
   */
  smt::Term find(const smt::Term & t) const;

  /** Clears the disjoint set
   */
  void clear();

 private:
  // Compare function for ranking
  bool (*comp)(const smt::Term & a, const smt::Term & b);

  // member to group's leader
  smt::UnorderedTermMap leader_;
  // group leader to group
  std::unordered_map<smt::Term, smt::UnorderedTermSet> group_;
};

}  // namespace smt
