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

void get_free_symbolic_consts(const smt::Term &term, smt::TermVec &out);


// -----------------------------------------------------------------------------

/** \class
 * UnsatcoreReducer class.
 * Implents an interative unsatcore reducer procedure. 
 *
 * reducer_solver is the solver that will be used for unsatcore extraction in
 * the procedure. It is different from the ext_solver (external solver used to
 * create the formula and assump)
 *
 */
class UnsatcoreReducer {
public:
  UnsatcoreReducer(smt::SmtSolver reducer_solver,
                   const smt::SmtSolver &ext_solver);
  ~UnsatcoreReducer();

  /** The main method to reduce the assump (vector of assumptions). The method
   *  assumes that the conjunction of the formula and assump is unsatisfiable.
   *  @param input formula
   *  @param input vector of assumptions
   *  @param output vector for the reduced assumptions
   *  @param output vector for the removed assumptions
   *  @param iter is the number of iterations done in the method. Default is 0,
   *    and it means that the result in out_red will be minimal.
   *  @param rand_seed if strickly positive then assump will be shuffled.
   */
  void reduce_assump_unsatcore(const smt::Term &formula,
                               const smt::TermVec &assump,
                               smt::TermVec &out_red,
                               smt::TermVec *out_rem = NULL,
                               unsigned iter = 0,
                               unsigned rand_seed = 0);

private:
  /** returns a label that will be used to precondition the assumption term 't'
   *  @param Input term t
   *  @return a boolean label for the term t
   */
  smt::Term label(const Term & t);

  smt::SmtSolver reducer_; // solver for unsatcore-based reduction
  smt::TermTranslator to_reducer_; // translator for converting terms from
                                   // ext_solver to reducer_

  smt::UnorderedTermMap labels_;  //< labels for unsat cores

};

}  // namespace smt
