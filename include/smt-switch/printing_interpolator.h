/*!
 * \file printing_interpolator.h
 * \brief Interpolator that wraps another and dumps the SMT-LIB of its
 *        queries
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_PRINTING_INTERPOLATOR_H
#define SMT_SWITCH_PRINTING_INTERPOLATOR_H

#include <cstddef>
#include <memory>
#include <ostream>
#include <string>
#include <vector>

#include "smt-switch/interpolator.h"
#include "smt-switch/printing_solver.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/term.h"

namespace smt {

/**
 * A class that wraps an interpolating solver and prints corresponding
 * SMT-LIB commands, writing each interpolation query as the wrapped
 * interpolator runs it, in its backend's syntax. It answers as the wrapped
 * interpolator does.
 */
class PrintingInterpolator : public AbsSmtInterpolator
{
 public:
  PrintingInterpolator(SmtInterpolator s, std::ostream * os);
  [[deprecated("use the constructor without a style")]] PrintingInterpolator(
      SmtInterpolator s, std::ostream * os, PrintingStyleEnum pse);
  PrintingInterpolator(const PrintingInterpolator & other) = default;
  PrintingInterpolator & operator=(const PrintingInterpolator & other) =
      default;

  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;

 protected:
  Result compute_interpolant(const Term & A,
                             const Term & B,
                             Term & out_I) const override;
  Result compute_seq_interpolants(const TermVec & formulae,
                                  TermVec & out_I) const override;
  void do_set_opt(const std::string & option,
                  const std::string & value) override;
  void reset_backend_assertions() override;
  void reset_backend() override;
  void forget_queries() override;
  void initialize() override;

  /* Runs a query on the wrapped interpolator, prints the commands it runs,
   * and stores the interpolants in out_I */
  Result print_query(const TermVec & formulae, TermVec & out_I) const;

  /* The wrapped interpolator */
  SmtInterpolator wrapped_interpolator;
  /* A stream to dump SMT-LIB commands to */
  std::ostream * out_stream;

  /* What the queries printed so far left in the wrapped interpolator */
  struct QueryRecord
  {
    /* Keep track of created names */
    std::size_t num_names = 0;
    /* For Bitwuzla and MathSAT, the formulae left asserted by the last
     * query, one context level each, and the names they were printed with */
    TermVec asserted = {};
    std::vector<std::string> asserted_names = {};
  };
  /* Shared by copies, as they share the wrapped interpolator */
  std::shared_ptr<QueryRecord> record = std::make_shared<QueryRecord>();
};

/* Returns a printing SmtInterpolator by wrapping PrintingInterpolator's
 * constructor.
 * @param wrapped_interpolator the interpolating solver to wrap
 * @param out_stream the stream to dump SMT-LIB to
 * @return an SmtInterpolator that dumps to out_stream each command that is
 *         executed, writing each interpolation query as wrapped_interpolator
 *         runs it, and answers as wrapped_interpolator does
 */
SmtInterpolator create_printing_interpolator(
    SmtInterpolator wrapped_interpolator, std::ostream * out_stream);

/* As create_printing_interpolator(wrapped_interpolator, out_stream); style
 * is ignored.
 */
[[deprecated("use create_printing_interpolator without a style")]]
SmtInterpolator create_printing_interpolator(
    SmtInterpolator wrapped_interpolator,
    std::ostream * out_stream,
    PrintingStyleEnum style);

}  // namespace smt

#endif  // SMT_SWITCH_PRINTING_INTERPOLATOR_H
