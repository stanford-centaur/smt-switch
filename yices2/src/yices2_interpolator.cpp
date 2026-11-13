/*!
 * \file yices2_interpolator.cpp
 * \brief An interpolating solver on Yices2's MCSAT
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Yices2 offers yices_check_context_with_interpolation, but that fixes every
 * symbol of B's models, and MCSAT cannot take the value of an array or a
 * function, so the same loop is run here over the shared symbols only.
 */
#include "smt-switch/yices2_interpolator.h"

#include <gmp.h>  // IWYU pragma: keep (required by yices.h)
#include <yices.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/solver_utils.h"
#include "smt-switch/sort.h"
#include "smt-switch/utils.h"
#include "smt-switch/yices2_extensions.h"
#include "smt-switch/yices2_solver.h"
#include "smt-switch/yices2_term.h"

namespace smt {

Yices2Interpolator::Yices2Interpolator()
    : AbsSmtInterpolator(InterpolatorKind::YICES2,
                         std::make_shared<Yices2Solver>())
{
}

void Yices2Interpolator::set_logic(const std::string l)
{
  AbsSmtInterpolator::set_logic(l);
  logic = l;
}

void Yices2Interpolator::do_set_opt(const std::string & option,
                                    const std::string & value)
{
  if (option == "produce-unsat-model-interpolants")
  {
    if (!bool_option_value(option, value))
    {
      throw IncorrectUsageException(
          "Yices2 interpolator cannot set " + option + " to " + value
          + ": it needs model interpolants to refute models of B");
    }
    return;
  }
  if (option == "produce-interpolants")
  {
    throw IncorrectUsageException(
        "The Yices2 interpolator does not allow the option " + option);
  }
  // the regular solver refuses what a Yices2 solver would
  backend_solver->set_opt(option, value);
  options.emplace_back(option, value);
}

void Yices2Interpolator::initialize()
{
  logic.clear();
  options.clear();
}

SmtSolver Yices2Interpolator::new_solver() const
{
  auto solver = std::make_shared<Yices2Solver>();
  // smt-switch has no option for the solver type
  if (yices_set_config(solver->get_config(), "solver-type", "mcsat") < 0)
  {
    throw InternalSolverException(detail::get_yices2_error());
  }
  solver->set_opt("incremental", "true");
  solver->set_opt("produce-unsat-model-interpolants", "true");
  if (!logic.empty())
  {
    solver->set_logic(logic);
  }
  for (const auto & [option, value] : options)
  {
    solver->set_opt(option, value);
  }
  return solver;
}

Result Yices2Interpolator::compute_interpolant(const Term & A,
                                               const Term & B,
                                               Term & out_I) const
{
  // Each model of B restricted to the shared symbols that A refutes gives a
  // formula A implies and the model falsifies, which B then has to satisfy
  // as well; once B cannot, their conjunction is the interpolant.
  SmtSolver solver_a, solver_b;
  std::vector<term_t> model_interpolants;
  while (true)
  {
    TermsPairVec model;
    Term model_interpolant;
    Result r = refute_model(A, B, solver_a, solver_b, model, model_interpolant);
    if (!r.is_unsat())
    {
      return r;
    }
    // unsat with no model interpolant: B has no model left
    if (!model_interpolant)
    {
      term_t I = yices_and(narrow_num_args(model_interpolants.size()),
                           model_interpolants.data());
      if (I == NULL_TERM)
      {
        throw InternalSolverException(detail::get_yices2_error());
      }
      out_I = std::make_shared<Yices2Term>(I);
      return r;
    }
    model_interpolants.push_back(
        std::static_pointer_cast<Yices2Term>(model_interpolant)->term);
  }
}

Result Yices2Interpolator::refute_model(const Term & A,
                                        const Term & B,
                                        SmtSolver & solver_a,
                                        SmtSolver & solver_b,
                                        TermsPairVec & model,
                                        Term & model_interpolant) const
{
  if (A->get_sort()->get_sort_kind() != BOOL
      || B->get_sort()->get_sort_kind() != BOOL)
  {
    throw IncorrectUsageException("get_interpolant requires boolean terms");
  }
  auto yices2_term = [](const Term & t) {
    return std::static_pointer_cast<Yices2Term>(t)->term;
  };

  UnorderedTermSet symbols_a, symbols_b;
  get_free_symbolic_consts(A, symbols_a);
  get_free_symbolic_consts(B, symbols_b);
  TermVec shared_symbols;
  std::vector<term_t> shared;
  for (const Term & symbol : symbols_a)
  {
    if (!symbols_b.count(symbol))
    {
      continue;
    }
    SortKind sk = symbol->get_sort()->get_sort_kind();
    if (sk != BOOL && sk != BV && sk != INT && sk != REAL)
    {
      throw NotImplementedException(
          "Yices2 interpolator cannot interpolate over " + symbol->to_string()
          + ", which both sides share: MCSAT fixes the shared symbols to "
            "their values in a model, and cannot fix a "
          + symbol->get_sort()->to_string());
    }
    shared_symbols.push_back(symbol);
    shared.push_back(yices2_term(symbol));
  }

  if (!solver_a)
  {
    solver_a = new_solver();
    solver_b = new_solver();
    solver_a->assert_formula(A);
    solver_b->assert_formula(B);
  }
  // for the Yices calls that have no AbsSmtSolver method
  context_t * ctx_a =
      std::static_pointer_cast<Yices2Solver>(solver_a)->get_context().get();
  context_t * ctx_b =
      std::static_pointer_cast<Yices2Solver>(solver_b)->get_context().get();

  Result r_b = solver_b->check_sat();
  if (!r_b.is_sat())
  {
    return r_b;
  }
  detail::Yices2ModelPtr model_b(yices_get_model(ctx_b, 1));
  if (!model_b)
  {
    throw InternalSolverException(detail::get_yices2_error());
  }
  for (std::size_t i = 0; i < shared.size(); ++i)
  {
    // an algebraic number has no term
    term_t value = yices_get_value_as_term(model_b.get(), shared[i]);
    model.emplace_back(
        shared_symbols[i],
        value == NULL_TERM ? Term() : std::make_shared<Yices2Term>(value));
  }

  smt_status_t status_a = yices_check_context_with_model(
      ctx_a,
      nullptr,
      model_b.get(),
      detail::narrow<uint32_t>(shared.size(), "a number of shared symbols"),
      shared.data());
  if (status_a == YICES_STATUS_SAT)
  {
    return Result(SAT);
  }
  if (status_a == YICES_STATUS_ERROR)
  {
    throw InternalSolverException(detail::get_yices2_error());
  }
  if (status_a != YICES_STATUS_UNSAT)
  {
    return Result(UNKNOWN,
                  "Yices2 could not decide a check while interpolating");
  }
  term_t refutation = yices_get_model_interpolant(ctx_a);
  if (refutation == NULL_TERM)
  {
    throw InternalSolverException(detail::get_yices2_error());
  }
  model_interpolant = std::make_shared<Yices2Term>(refutation);
  solver_b->assert_formula(model_interpolant);
  return Result(UNSAT);
}

Result Yices2Interpolator::compute_seq_interpolants(const TermVec & formulae,
                                                    TermVec & out_I) const
{
  return sequence_from_interpolants(formulae, out_I);
}

}  // namespace smt
