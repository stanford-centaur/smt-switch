/*!
 * \file unsat_core_reducer.h
 * \brief Reducer that shrinks unsatisfiable sets of assumptions
 * \author Ahmed Irfan
 * \author Hongce Zhang
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_UNSAT_CORE_REDUCER_H
#define SMT_SWITCH_UNSAT_CORE_REDUCER_H

#include "smt-switch/smt_defs.h"
#include "smt-switch/term_translator.h"

namespace smt {

/** \class
 * UnsatcoreReducer class.
 * Implements an iterative unsatcore reducer procedure.
 *
 * reducer_solver is the solver that will be used for unsatcore extraction in
 * the procedure. It is different from the ext_solver (external solver used to
 * create the formula and assump)
 *
 */
class UnsatCoreReducer
{
 public:
  explicit UnsatCoreReducer(SmtSolver reducer_solver);

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
   *  @throws SolverException if the reducer answers unknown
   */
  bool reduce_assump_unsatcore(const Term & formula,
                               const TermVec & assump,
                               TermVec & out_red,
                               TermVec * out_rem = nullptr,
                               unsigned iter = 0,
                               unsigned rand_seed = 0);

  /** The additional method to reduce the assump (vector of assumptions). The
   * method assumes that the conjunction of the formula and assump is
   * unsatisfiable. This will iterate through the assump and requires at most
   * size(assump) queries.
   *  @param input formula
   *  @param input vector of assumptions
   *  @param output vector for the reduced assumptions
   *  @param output vector for the removed assumptions
   *  @param iter is the number of iterations done in the method. Default is 0,
   *         and it means that the result in out_red will be minimal.
   *  returns false if the formula conjoined with the assump is satisfiable,
   *          otherwise returns true
   *  @throws IncorrectUsageException if an assumption appears more than once
   *  @throws SolverException if the reducer answers unknown
   */
  bool linear_reduce_assump_unsatcore(const Term & formula,
                                      const TermVec & assump,
                                      TermVec & out_red,
                                      TermVec * out_rem = nullptr,
                                      unsigned iter = 0);

  /** This clears the term translation cache. Note, term translator is used to
   *  translate the terms of the external solver to the
   *  unsat-assumption-reducer-solver. A use-case of this method is to call it
   * before calling the reduce_assump_unsat from one call to another call when
   * the external solver in the first call is different from the second call.
   */
  void clear_term_translation_cache();

 private:
  /** returns a label that will be used to precondition the assumption term 't'
   *  @param Input term t
   *  return a boolean label for the term t
   */
  Term label(const Term & t);

  SmtSolver reducer_;             ///< solver for unsatcore-based reduction
  TermTranslator to_reducer_;     ///< translator for converting terms from
                                  ///< ext_solver to reducer_
  UnorderedTermMap labels_ = {};  ///< labels for unsat cores
};

}  // namespace smt

#endif  // SMT_SWITCH_UNSAT_CORE_REDUCER_H
