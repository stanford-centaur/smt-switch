/*!
 * \file msat_interpolator.cpp
 * \brief MathSAT implementation of AbsSmtInterpolator
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/msat_interpolator.h"

#include <mathsat.h>

#include <cstddef>
#include <memory>
#include <string>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/msat_env.h"
#include "smt-switch/msat_extensions.h"
#include "smt-switch/msat_solver.h"
#include "smt-switch/msat_term.h"
#include "smt-switch/result.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/term.h"

using namespace std;

namespace smt {

/** text, followed by error if there is one */
static string with_error(const string & text, const string & error)
{
  return error.empty() ? text : text + ": " + error;
}

MsatInterpolator::MsatInterpolator()
    : AbsSmtInterpolator(MSAT_INTERPOLATOR, std::make_shared<MsatSolver>()),
      msat_solver_(std::static_pointer_cast<MsatSolver>(backend_solver))
{
  initialize();
}

void MsatInterpolator::initialize()
{
  // without interpolation there are no interpolants, and the eager BV
  // solver produces no proofs
  msat_solver_->set_opt("interpolation", "true");
  msat_solver_->set_opt("theory.bv.eager", "false");
  // only a preference, which a caller's own set_opt replaces
  msat_solver_->set_opt("theory.bv.bit_blast_mode", "0");
  // TODO: decide if we should add this
  // msat_solver_->set_opt("theory.eq_propagation", "false");
}

void MsatInterpolator::do_set_opt(const string & option, const string & value)
{
  // The constructor sets these, and the interpolator cannot do without them.
  const string name = detail::msat_option_name(option);
  if (name == "interpolation" || name == "theory.bv.eager")
  {
    throw IncorrectUsageException(
        "The MathSAT interpolator does not allow the option " + option);
  }
  msat_solver_->set_opt(option, value);
}

// delegate the interpolation procedure to `compute_seq_interpolants`
Result MsatInterpolator::compute_interpolant(const Term & A,
                                             const Term & B,
                                             Term & out_I) const
{
  return interpolant_from_sequence(A, B, out_I);
}

// Compute interpolation sequence with incremental solving.
// The function tries to reuse as many previously-asserted formulas as possible.
// To achieve this, an assertion stack is maintained, where each assertion
// is associated with a context level (backtrack point in MathSAT) and an
// interpolation group.
//
// Before SMT solving, the function scans the assertion stack and the current
// input formulae in order, checking if they match at each position.
// Specifically, the i-th element on the assertion stack must match the i-th
// element in the input formulae. If they match, the assertion can be reused;
// otherwise, the function backtracks the solver to the point where the match
// ends and asserts the remaining formulas from that point onward.
//
// The following invariant should hold before and after the call:
// `#backtrack-points == last_itp_query_assertions_.size() == itp_grps_.size()`
Result MsatInterpolator::compute_seq_interpolants(const TermVec & formulae,
                                                  TermVec & out_I) const
{
  const std::shared_ptr<MsatEnv> & env = msat_solver_->env_wrapper_.get_env();

  // unwrapped before anything changes, so a refused formula leaves the
  // assertion stack as it was
  vector<msat_term> mformulae;
  mformulae.reserve(formulae.size());
  for (const Term & f : formulae)
  {
    mformulae.push_back(msat_solver_->get_msat_term(f)->term);
  }

  // count how many assertions can be reused, unless reuse is off
  size_t num_reused = 0;
  while (incremental_mode && num_reused < last_itp_query_assertions_.size()
         && num_reused < formulae.size()
         && last_itp_query_assertions_.at(num_reused)
                == formulae.at(num_reused))
  {
    ++num_reused;
  }

  // pop formulas that cannot be reused
  if (num_reused == 0)
  {
    // no reusable formulas, simply reset
    msat_reset_env(*env);
  }
  else
  {
    for (size_t i = num_reused; i < last_itp_query_assertions_.size(); ++i)
    {
      msat_pop_backtrack_point(*env);
    }
  }

  // update the interpolation groups and assertions
  itp_grps_.resize(num_reused);
  itp_grps_.reserve(formulae.size());
  last_itp_query_assertions_.resize(num_reused);
  last_itp_query_assertions_.reserve(formulae.size());

  // add new assertions from formulas
  for (size_t k = num_reused; k < formulae.size(); ++k)
  {
    // Add a new interpolation group and a new backtrack point
    // then push the formula.
    int grp = msat_create_itp_group(*env);
    msat_set_itp_group(*env, grp);
    msat_push_backtrack_point(*env);
    msat_assert_formula(*env, mformulae.at(k));
    itp_grps_.push_back(grp);
    last_itp_query_assertions_.push_back(formulae.at(k));
  }

  // solve query and get interpolants
  bool timed_out = false;
  msat_result msat_res = msat_solver_->solve(nullptr, timed_out);

  if (msat_res == MSAT_SAT)
  {
    return Result(SAT);
  }
  else if (msat_res == MSAT_UNKNOWN)
  {
    if (timed_out)
    {
      return Result(UNKNOWN, "Time limit reached.");
    }
    return Result(
        UNKNOWN,
        with_error("Interpolation failure", detail::last_error_message(*env)));
  }

  Result r = Result(UNSAT);
  for (size_t i = 1; i < itp_grps_.size(); ++i)
  {
    msat_term mI = msat_get_interpolant(*env, itp_grps_.data(), i);
    if (MSAT_ERROR_TERM(mI))
    {
      // add a null term -- see solver.h documentation for this function
      Term nullterm;
      out_I.push_back(nullterm);
      // MathSAT reports the error behind an error term, and the first
      // failure's report explains the result
      if (r.is_unsat())
      {
        r = Result(UNKNOWN,
                   with_error("Had at least one interpolation failure in "
                              "get_sequence_interpolants",
                              detail::last_error_message(*env)));
      }
    }
    else
    {
      out_I.push_back(make_shared<MsatTerm>(env, mI));
    }
  }

  return r;
}

void MsatInterpolator::forget_queries()
{
  last_itp_query_assertions_.clear();
  itp_grps_.clear();
}

}  // namespace smt
