/*!
 * \file yices2_interpolating_solver.h
 * \brief An interpolating solver on Yices2's MCSAT
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_YICES2_INTERPOLATING_SOLVER_H
#define SMT_SWITCH_YICES2_INTERPOLATING_SOLVER_H

#include <string>
#include <utility>
#include <vector>

#include "smt-switch/interpolating_solver.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/term.h"

namespace smt {

/** Interpolates with MCSAT, the solver Yices2 has only when it is built
 *  with it; see Yices2SolverFactory::create_interpolating_solver. MCSAT finds
 *  an interpolant by refuting, one after another, models of B that it
 *  restricts to the symbols A and B share.
 *
 *  It interpolates over Booleans, bit-vectors, and integer and real
 *  arithmetic, nonlinear arithmetic included. A symbol both sides share
 *  must have one of those sorts: MCSAT fixes the shared symbols to their
 *  values in a model, and cannot fix an array, a function or a symbol of
 *  an uninterpreted sort, so a query sharing one throws
 *  NotImplementedException. Such a symbol on one side only is fine.
 */
class Yices2InterpolatingSolver : public AbsSmtInterpolator
{
 public:
  Yices2InterpolatingSolver();
  Yices2InterpolatingSolver(const Yices2InterpolatingSolver &) = delete;
  Yices2InterpolatingSolver & operator=(const Yices2InterpolatingSolver &) =
      delete;

  /** Sets the logic of the terms and of the queries */
  void set_logic(const std::string logic) override;

 protected:
  Result compute_interpolant(const Term & A,
                             const Term & B,
                             Term & out_I) const override;
  Result compute_seq_interpolants(const TermVec & formulae,
                                  TermVec & out_I) const override;
  void do_set_opt(const std::string & option,
                  const std::string & value) override;

  void initialize() override;

  /** @throws NotImplementedException if a symbol both sides share has a
   *          sort MCSAT cannot fix
   */
  Result refute_model(const Term & A,
                      const Term & B,
                      SmtSolver & solver_a,
                      SmtSolver & solver_b,
                      TermsPairVec & model,
                      Term & model_interpolant) const override;

 private:
  /** @return a solver to check A or B of a query with */
  SmtSolver new_solver() const;

  std::string logic = "";  ///< empty until set_logic
  std::vector<std::pair<std::string, std::string>>
      options = {};  ///< in the order they were set
};

}  // namespace smt

#endif  // SMT_SWITCH_YICES2_INTERPOLATING_SOLVER_H
