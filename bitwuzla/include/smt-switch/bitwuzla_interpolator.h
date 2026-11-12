/*!
 * \file bitwuzla_interpolator.h
 * \brief Bitwuzla implementation of AbsSmtInterpolator
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_BITWUZLA_INTERPOLATOR_H
#define SMT_SWITCH_BITWUZLA_INTERPOLATOR_H

#include <cstdint>
#include <memory>
#include <string>

#include "smt-switch/bitwuzla_solver.h"
#include "smt-switch/interpolator.h"
#include "smt-switch/term.h"

namespace smt {

class BzlaInterpolator : public AbsSmtInterpolator
{
 public:
  BzlaInterpolator();
  BzlaInterpolator(const BzlaInterpolator &) = delete;
  BzlaInterpolator & operator=(const BzlaInterpolator &) = delete;

 protected:
  Result compute_interpolant(const Term & A,
                             const Term & B,
                             Term & out_I) const override;
  Result compute_seq_interpolants(const TermVec & formulae,
                                  TermVec & out_I) const override;
  void do_set_opt(const std::string & option,
                  const std::string & value) override;
  void forget_queries() override;
  // enables interpolation, on construction and after reset()
  void initialize() override;

  // the regular solver that builds this solver's terms
  std::shared_ptr<BzlaSolver> bzla_solver;

  // assertions from the last interpolation query, indexed by the context level
  // (although one can get assertions using `bzla->get_assertions()`,
  // the method does not guarantee that the assertions are in the correct order)
  mutable TermVec last_itp_query_assertions = {};

  std::string dump_queries_prefix = "";
  mutable uint32_t itp_query_count = 0;
};

using BzlaInterpolatingSolver [[deprecated("use BzlaInterpolator")]] =
    BzlaInterpolator;

}  // namespace smt

#endif  // SMT_SWITCH_BITWUZLA_INTERPOLATOR_H
