/*!
 * \file msat_interpolator.h
 * \brief MathSAT implementation of AbsSmtInterpolator
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_MSAT_INTERPOLATOR_H
#define SMT_SWITCH_MSAT_INTERPOLATOR_H

#include <memory>
#include <string>
#include <vector>

#include "smt-switch/interpolator.h"
#include "smt-switch/msat_solver.h"
#include "smt-switch/term.h"

namespace smt {

class MsatInterpolator : public AbsSmtInterpolator
{
 public:
  MsatInterpolator();
  MsatInterpolator(const MsatInterpolator &) = delete;
  MsatInterpolator & operator=(const MsatInterpolator &) = delete;

 protected:
  Result compute_interpolant(const Term & A,
                             const Term & B,
                             Term & out_I) const override;
  Result compute_seq_interpolants(const TermVec & formulae,
                                  TermVec & out_I) const override;
  void do_set_opt(const std::string & option,
                  const std::string & value) override;
  void forget_queries() override;
  // sets the options MathSAT cannot interpolate without and the solver's
  // preferences, on construction and after reset()
  void initialize() override;

  // the regular solver that builds this solver's terms
  std::shared_ptr<MsatSolver> msat_solver_;

  // assertions from the last interpolation query, indexed by the context level
  // (although one can get assertions using `msat_get_asserted_formulas`,
  // the method does not guarantee that the assertions are in the correct order)
  mutable TermVec last_itp_query_assertions_ = {};
  // interpolation group for each assertion level
  mutable std::vector<int> itp_grps_ = {};
};

using MsatInterpolatingSolver [[deprecated("use MsatInterpolator")]] =
    MsatInterpolator;

}  // namespace smt

#endif  // SMT_SWITCH_MSAT_INTERPOLATOR_H
