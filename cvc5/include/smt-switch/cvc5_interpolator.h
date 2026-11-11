/*!
 * \file cvc5_interpolator.h
 * \brief cvc5 implementation of AbsSmtInterpolator
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_CVC5_INTERPOLATOR_H
#define SMT_SWITCH_CVC5_INTERPOLATOR_H

#include <memory>
#include <string>

#include "smt-switch/cvc5_solver.h"
#include "smt-switch/interpolator.h"

namespace smt {

class Cvc5Interpolator : public AbsSmtInterpolator
{
 public:
  Cvc5Interpolator();
  Cvc5Interpolator(const Cvc5Interpolator &) = delete;
  Cvc5Interpolator & operator=(const Cvc5Interpolator &) = delete;

 protected:
  Result compute_interpolant(const Term & A,
                             const Term & B,
                             Term & out_I) const override;
  Result compute_seq_interpolants(const TermVec & formulae,
                                  TermVec & out_I) const override;
  void do_set_opt(const std::string & option,
                  const std::string & value) override;
  // sets the options interpolation needs, on construction and after reset()
  void initialize() override;

  // the regular solver that builds this solver's terms
  std::shared_ptr<Cvc5Solver> cvc5_solver;
};

using cvc5InterpolatingSolver [[deprecated("use Cvc5Interpolator")]] =
    Cvc5Interpolator;

}  // namespace smt

#endif  // SMT_SWITCH_CVC5_INTERPOLATOR_H
