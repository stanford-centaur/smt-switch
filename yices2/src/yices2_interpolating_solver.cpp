/*!
 * \file yices2_interpolating_solver.cpp
 * \brief An interpolating solver on Yices2's MCSAT.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Yices2 offers yices_check_context_with_interpolation, but that fixes every
 * symbol of B's models, and MCSAT cannot take the value of an array or a
 * function, so the same loop is run here over the shared symbols only.
 */

#include "yices2_interpolating_solver.h"

#include <gmp.h>  // IWYU pragma: keep (required by yices.h)
#include <yices.h>

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "exceptions.h"
#include "solver_utils.h"
#include "sort.h"
#include "utils.h"
#include "yices2_solver.h"
#include "yices2_term.h"

namespace smt {

namespace {

// Yices2's last error, which it hands over as a string to free
std::string yices2_error()
{
  char * reason = yices_error_string();
  std::string message(reason);
  yices_free_string(reason);
  return message;
}

struct ContextDeleter
{
  void operator()(context_t * ctx) const { yices_free_context(ctx); }
};
using ContextPtr = std::unique_ptr<context_t, ContextDeleter>;

struct ModelDeleter
{
  void operator()(model_t * model) const { yices_free_model(model); }
};
using ModelPtr = std::unique_ptr<model_t, ModelDeleter>;

// An MCSAT context for one side of a query, which is checked again after
// each refuted model. A's also produces the interpolants of its refutations.
ContextPtr new_context(bool model_interpolation)
{
  ctx_config_t * config = yices_new_config();
  if (yices_set_config(config, "solver-type", "mcsat") < 0
      || yices_set_config(config, "mode", "multi-checks") < 0
      || (model_interpolation
          && yices_set_config(config, "model-interpolation", "true") < 0))
  {
    std::string message = yices2_error();
    yices_free_config(config);
    throw InternalSolverException(message);
  }
  ContextPtr ctx(yices_new_context(config));
  yices_free_config(config);
  if (!ctx)
  {
    throw InternalSolverException(yices2_error());
  }
  return ctx;
}

void assert_into(context_t * ctx, term_t t)
{
  if (yices_assert_formula(ctx, t) < 0)
  {
    throw InternalSolverException(yices2_error());
  }
}

// what a check that neither proved nor refuted answers
Result undecided(smt_status_t status)
{
  if (status == YICES_STATUS_ERROR)
  {
    throw InternalSolverException(yices2_error());
  }
  return Result(UNKNOWN, "Yices2 could not decide a check while interpolating");
}

}  // namespace

Yices2InterpolatingSolver::Yices2InterpolatingSolver()
    : AbsSmtInterpolator(YICES2_INTERPOLATOR, std::make_shared<Yices2Solver>())
{
}

void Yices2InterpolatingSolver::do_set_opt(const std::string & option,
                                           const std::string & /* value */)
{
  if (option == "produce-interpolants")
  {
    throw IncorrectUsageException("Yices2 interpolator does not allow option: "
                                  + option);
  }
  // each query runs in contexts of its own, which no option reaches
  throw NotImplementedException("Yices2 interpolator does not take option: "
                                + option);
}

Result Yices2InterpolatingSolver::get_interpolant(const Term & A,
                                                  const Term & B,
                                                  Term & out_I) const
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
    shared.push_back(yices2_term(symbol));
  }

  ContextPtr ctx_a = new_context(true);
  ContextPtr ctx_b = new_context(false);
  assert_into(ctx_a.get(), yices2_term(A));
  assert_into(ctx_b.get(), yices2_term(B));

  // Each model of B restricted to the shared symbols that A refutes gives a
  // formula A implies and the model falsifies, which B then has to satisfy
  // as well; once B cannot, their conjunction is the interpolant.
  std::vector<term_t> model_interpolants;
  while (true)
  {
    smt_status_t status_b = yices_check_context(ctx_b.get(), nullptr);
    if (status_b == YICES_STATUS_UNSAT)
    {
      term_t I = yices_and(narrow_num_args(model_interpolants.size()),
                           model_interpolants.data());
      if (I == NULL_TERM)
      {
        throw InternalSolverException(yices2_error());
      }
      out_I = std::make_shared<Yices2Term>(I);
      return Result(UNSAT);
    }
    if (status_b != YICES_STATUS_SAT)
    {
      return undecided(status_b);
    }

    ModelPtr model(yices_get_model(ctx_b.get(), 1));
    if (!model)
    {
      throw InternalSolverException(yices2_error());
    }
    smt_status_t status_a = yices_check_context_with_model(
        ctx_a.get(),
        nullptr,
        model.get(),
        detail::narrow<uint32_t>(shared.size(), "a number of shared symbols"),
        shared.data());
    if (status_a == YICES_STATUS_SAT)
    {
      return Result(SAT);
    }
    if (status_a != YICES_STATUS_UNSAT)
    {
      return undecided(status_a);
    }

    term_t model_interpolant = yices_get_model_interpolant(ctx_a.get());
    if (model_interpolant == NULL_TERM)
    {
      throw InternalSolverException(yices2_error());
    }
    model_interpolants.push_back(model_interpolant);
    assert_into(ctx_b.get(), model_interpolant);
  }
}

Result Yices2InterpolatingSolver::get_sequence_interpolants(
    const TermVec & formulae, TermVec & out_I) const
{
  return sequence_from_interpolants(formulae, out_I);
}

}  // namespace smt
