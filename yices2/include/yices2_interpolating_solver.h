/*!
 * \file yices2_interpolating_solver.h
 * \brief An interpolating solver on Yices2's MCSAT.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#pragma once

#include <string>
#include <utility>
#include <vector>

#include "interpolating_solver.h"
#include "result.h"
#include "smt_defs.h"
#include "term.h"

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

  Result get_interpolant(const Term & A,
                         const Term & B,
                         Term & out_I) const override;
  Result get_sequence_interpolants(const TermVec & formulae,
                                   TermVec & out_I) const override;

  /** Sets the logic of the terms and of the queries */
  void set_logic(const std::string logic) override;

 protected:
  void do_set_opt(const std::string & option,
                  const std::string & value) override;

  void initialize() override;

 private:
  /** @return a solver to check A or B of a query with */
  SmtSolver new_solver() const;

  std::string logic;  ///< empty until set_logic
  std::vector<std::pair<std::string, std::string>>
      options;  ///< in the order they were set
};

}  // namespace smt
