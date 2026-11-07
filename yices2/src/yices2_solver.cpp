/*********************                                                        */
/*! \file yices2_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson, Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Yices2 implementation of AbsSmtSolver
**
**
**/

#include "yices2_solver.h"

#include <gmp.h>
#include <signal.h>
#include <sys/time.h>
#include <yices.h>

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "exceptions.h"
#include "ops.h"
#include "result.h"
#include "solver_enums.h"
#include "solver_utils.h"
#include "utils.h"
#include "yices2_extensions.h"
#include "yices2_sort.h"
#include "yices2_term.h"

using namespace std;

namespace smt {

// Shared with yices2_timelimit_handler, which runs on a signal. Both are
// volatile so the compiler cannot hold either in a register across the search,
// and the flag is a sig_atomic_t because that is the only type whose write
// from a handler the standard promises will be visible here.
context_t * volatile running_ctx = nullptr;
volatile sig_atomic_t yices2_terminated = 0;

// Registered for SIGALRM alone, so the argument cannot be anything else and is
// not worth naming. Only async-signal-safe work belongs here: a comparison,
// yices_stop_search, which Yices documents as the way to interrupt a search,
// and a flag store. An assert would not qualify -- it reaches fprintf -- and
// would be compiled out of a release build besides, leaving the null context
// it was meant to catch to reach Yices.
void yices2_timelimit_handler(int /* signum */)
{
  if (running_ctx != nullptr)
  {
    yices_stop_search(running_ctx);
    yices2_terminated = 1;
  }
}

namespace {

// frees a context, keeping the Yices instance alive until then
struct ContextDeleter
{
  Yices2InstanceRef instance = {};
  void operator()(context_t * c) const { yices_free_context(c); }
};

}  // namespace

/* Yices2Solver implementation */

Yices2Solver::Yices2Solver() : AbsSmtSolver(YICES2), config(yices_new_config())
{
}

Yices2Solver::~Yices2Solver() { yices_free_config(config); }

void Yices2Solver::set_opt(const std::string option, const std::string value)
{
  if (option == "produce-models")
  {
    if (value == "false")
    {
      std::cout << "Warning: Yices2 backend always produces models -- it "
                   "can't be disabled."
                << std::endl;
    }
  }
  else if (option == "incremental")
  {
    if (ctx)
    {
      throw IncorrectUsageException(
          "Yices2 can only set incremental before the first assertion, "
          "check or push");
    }
    if (value == "false")
    {
      yices_set_config(config, "mode", "one-shot");
    }
    else if (value == "true")
    {
      yices_set_config(config, "mode", "push-pop");
    }
  }
  else if (option == "time-limit")
  {
    time_limit = stod(value);
  }
  else if (option == "produce-unsat-assumptions")
  {
    // nothing to be done
  }
  else if (option == "produce-unsat-model-interpolants")
  {
    if (ctx)
    {
      throw IncorrectUsageException(
          "Yices2 can only set produce-unsat-model-interpolants before the "
          "first assertion, check or push");
    }
    if (value != "true" && value != "false")
    {
      throw IncorrectUsageException("Invalid value for boolean option "
                                    + option);
    }
    if (yices_set_config(config, "model-interpolation", value.c_str()) < 0)
    {
      throw InternalSolverException(take_yices_error());
    }
  }
  else
  {
    string msg("Option ");
    msg += option;
    msg += " is not yet supported for the Yices2 backend";
    throw NotImplementedException(msg);
  }
}

/** The smt-switch term of res
 *  @throws InternalSolverException where making res failed
 */
static Term checked_term(term_t res)
{
  if (yices_error_code() != 0)
  {
    throw InternalSolverException(take_yices_error());
  }
  return std::make_shared<Yices2Term>(res);
}

void Yices2Solver::set_logic(const std::string logic)
{
  if (ctx)
  {
    throw IncorrectUsageException(
        "Yices2 can only set the logic before the first assertion, check or "
        "push");
  }
  // Without MCSAT, Yices2 2.6.0 accepts a nonlinear logic and then makes a
  // context without arithmetic.
  if (!yices_has_mcsat())
  {
    for (const auto arithmetic : { "NIA", "NRA", "NIRA" })
    {
      if (logic.find(arithmetic) != std::string::npos)
      {
        throw IncorrectUsageException("Yices2 cannot use logic " + logic
                                      + ": it was built without MCSAT");
      }
    }
  }
  // Yices cannot copy a configuration, so try the logic on a scratch one
  // first; a logic Yices rejects, such as one this build does not support,
  // then leaves the configuration as it was
  ctx_config_t * scratch_config = yices_new_config();
  context_t * scratch_ctx = nullptr;
  if (yices_default_config_for_logic(scratch_config, logic.c_str()) == 0)
  {
    scratch_ctx = yices_new_context(scratch_config);
  }
  yices_free_config(scratch_config);
  if (!scratch_ctx)
  {
    throw IncorrectUsageException("Yices2 cannot use logic " + logic + ": "
                                  + take_yices_error());
  }
  yices_free_context(scratch_ctx);

  yices_default_config_for_logic(config, logic.c_str());
  logic_ = logic;
}

std::shared_ptr<context_t> Yices2Solver::get_context()
{
  if (!ctx)
  {
    context_t * c = yices_new_context(config);
    if (!c)
    {
      throw IncorrectUsageException(
          "Yices2 cannot create a context with the logic and options set: "
          + take_yices_error());
    }
    ctx = std::shared_ptr<context_t>(c, ContextDeleter());
  }
  return ctx;
}

ctx_config_t * Yices2Solver::get_config() { return config; }

Term Yices2Solver::make_term(bool b) const
{
  term_t y_term;
  if (b)
  {
    y_term = yices_true();
  }
  else
  {
    y_term = yices_false();
  }

  return checked_term(y_term);
}

Term Yices2Solver::make_term(int64_t i, const Sort & sort) const
{
  SortKind sk = sort->get_sort_kind();
  term_t y_term;
  if (sk == INT || sk == REAL)
  {
    y_term = yices_int64(i);
  }
  else if (sk == BV)
  {
    y_term = yices_bvconst_int64(narrow_width(sort->get_width()), i);
  }
  else
  {
    string msg("Can't create value ");
    msg += std::to_string(i);
    msg += " with sort ";
    msg += sort->to_string();
    throw IncorrectUsageException(msg);
  }

  return checked_term(y_term);
}

Term Yices2Solver::make_term(const std::string val,
                             const Sort & sort,
                             uint64_t base) const
{
  term_t y_term;

  SortKind sk = sort->get_sort_kind();
  if (sk == BV)
  {
    y_term = ext_yices_make_bv_number(
        val.c_str(), sort->get_width(), detail::narrow<int>(base, "a base"));
  }
  else if (sk == REAL)
  {
    if (base != 10)
    {
      throw NotImplementedException("Does not support base not equal to 10.");
    }

    std::string msg =
        "Can't create value " + val + " with sort " + sort->to_string();
    if (!is_arith_number(REAL, val))
    {
      throw IncorrectUsageException(msg);
    }
    // yices_parse_float reads only a leading number, so "1/2" as 1, while
    // yices_parse_rational reads no decimals
    y_term = val.find('/') == std::string::npos
                 ? yices_parse_float(val.c_str())
                 : yices_parse_rational(val.c_str());
    if (y_term == NULL_TERM)
    {
      // such as division by zero
      yices_clear_error();
      throw IncorrectUsageException(msg);
    }
  }
  else if (sk == INT)
  {
    // reads an integer of any size, but also a fraction, which is no Int
    y_term = yices_parse_rational(val.c_str());
    if (y_term == NULL_TERM || !yices_term_is_int(y_term))
    {
      yices_clear_error();
      throw IncorrectUsageException("Can't create value " + val + " with sort "
                                    + sort->to_string());
    }
  }
  else
  {
    string msg("Can't create value ");
    msg += val;
    msg += " with sort ";
    msg += sort->to_string();
    throw IncorrectUsageException(msg);
  }

  return checked_term(y_term);
}

Term Yices2Solver::make_term(const Term & val, const Sort & sort) const
{
  // Yices writes a constant array as (lambda (i) val) and reduces any
  // application of one, so reading and storing work. What its context will
  // not hold is such a lambda equated with an uninterpreted array, and its
  // model cannot evaluate the array itself; get_array_values says so.
  if (sort->get_sort_kind() != ARRAY)
  {
    throw IncorrectUsageException("Expecting an array sort but got "
                                  + sort->to_string());
  }
  shared_ptr<Yices2Sort> ysort = backend_pointer_cast<Yices2Sort>(sort);
  shared_ptr<Yices2Term> yval = backend_pointer_cast<Yices2Term>(val);

  // a variable, not an uninterpreted term: yices_lambda takes only the first
  term_t index = yices_new_variable(yices_type_child(ysort->get_ytype(), 0));
  term_t y_term = yices_lambda(1, &index, yval->term);
  if (y_term == NULL_TERM)
  {
    throw InternalSolverException(take_yices_error());
  }
  return std::make_shared<Yices2Term>(y_term);
}

void Yices2Solver::assert_formula(const Term & t)
{
  shared_ptr<Yices2Term> yterm = backend_pointer_cast<Yices2Term>(t);
  if (!yices_type_is_bool(yices_type_of_term(yterm->term)))
  {
    throw IncorrectUsageException("Attempted to assert non-boolean to solver: "
                                  + t->to_string());
  }

  yices_assert_formula(get_context().get(), yterm->term);
  if (yices_error_code() != 0)
  {
    throw InternalSolverException(take_yices_error());
  }
  assertions.push_back(t);
}

Result Yices2Solver::check_sat()
{
  timelimit_start();
  smt_status_t res = yices_check_context(get_context().get(), NULL);
  bool tl_triggered = timelimit_end();

  if (yices_error_code() != 0)
  {
    throw InternalSolverException(take_yices_error());
  }

  if (res == YICES_STATUS_SAT)
  {
    return Result(SAT);
  }
  else if (res == YICES_STATUS_UNSAT)
  {
    return Result(UNSAT);
  }
  else if (tl_triggered)
  {
    return Result(UNKNOWN, "Time limit reached.");
  }
  else
  {
    return Result(UNKNOWN);
  }
}

Result Yices2Solver::do_check_sat_assuming(const TermVec & assumptions)
{
  vector<term_t> y_assumps;
  y_assumps.reserve(assumptions.size());
  for (const Term & a : assumptions)
  {
    y_assumps.push_back(backend_pointer_cast<Yices2Term>(a)->term);
  }

  timelimit_start();
  smt_status_t res = yices_check_context_with_assumptions(
      get_context().get(),
      NULL,
      detail::narrow<uint32_t>(y_assumps.size(), "a number of assumptions"),
      y_assumps.data());
  bool tl_triggered = timelimit_end();

  if (yices_error_code() != 0)
  {
    throw InternalSolverException(take_yices_error());
  }

  if (res == YICES_STATUS_SAT)
  {
    return Result(SAT);
  }
  else if (res == YICES_STATUS_UNSAT)
  {
    return Result(UNSAT);
  }
  else if (tl_triggered)
  {
    return Result(UNKNOWN, "Time limit reached.");
  }
  else
  {
    return Result(UNKNOWN);
  }
}

void Yices2Solver::do_push(uint64_t num)
{
  scope_starts.insert(scope_starts.end(), num, assertions.size());
  if (yices_context_status(get_context().get()) == YICES_STATUS_UNSAT)
  {
    pushes_after_unsat += num;
    return;
  }

  for (size_t i = 0; i < num; ++i)
  {
    yices_push(get_context().get());
  }
}

void Yices2Solver::do_pop(uint64_t num)
{
  for (size_t i = 0; i < num; ++i)
  {
    if (pushes_after_unsat)
    {
      pushes_after_unsat--;
      continue;
    }
    yices_pop(get_context().get());
  }
  assertions.resize(scope_starts[scope_starts.size() - num]);
  scope_starts.resize(scope_starts.size() - num);
}

Term Yices2Solver::get_value(const Term & t) const
{
  shared_ptr<Yices2Term> yterm = backend_pointer_cast<Yices2Term>(t);
  model_t * model = ctx ? yices_get_model(ctx.get(), true) : nullptr;
  if (!model)
  {
    yices_clear_error();
    throw IncorrectUsageException(
        "Last call to check_sat was not sat, cannot get a model.");
  }

  if (!yices_term_is_function(yterm->term))
  {
    term_t value = yices_get_value_as_term(model, yterm->term);
    if (value == NULL_TERM)
    {
      // the model declines some terms, one containing a lambda among them,
      // and a term built from NULL_TERM only fails later and further away
      throw NotImplementedException("Yices2 cannot evaluate "
                                    + yterm->to_string()
                                    + " in a model: " + take_yices_error());
    }
    return std::make_shared<Yices2Term>(value);
  }
  else
  {
    throw NotImplementedException(
        "Yices does not convert a function or array value into a term: "
        "yices_get_value_as_term fails for a function type. Use "
        "get_array_values for an array, or get_value on a select of it.");
  }
}

/* Turn one model node back into a term of the given sort. Yices reports
 * model values as yval_t nodes and has no generic node-to-term conversion,
 * so each one goes through the string form make_term already reads.
 */
static Term term_from_yval(const Yices2Solver & solver,
                           model_t * model,
                           const yval_t & node,
                           const Sort & sort)
{
  switch (node.node_tag)
  {
    case YVAL_BOOL: {
      int32_t b = 0;
      if (yices_val_get_bool(model, &node, &b) < 0)
      {
        throw InternalSolverException(take_yices_error());
      }
      return solver.make_term(b != 0);
    }
    case YVAL_BV: {
      uint32_t width = yices_val_bitsize(model, &node);
      std::vector<int32_t> bits(width);
      if (yices_val_get_bv(model, &node, bits.data()) < 0)
      {
        throw InternalSolverException(take_yices_error());
      }
      // bits[0] is the low-order bit, so read the array back to front
      std::string digits;
      for (uint32_t pos = width; pos > 0; pos--)
      {
        digits += bits[pos - 1] ? '1' : '0';
      }
      return solver.make_term(digits, sort, 2);
    }
    case YVAL_RATIONAL: {
      int64_t num = 0;
      uint64_t den = 0;
      if (yices_val_get_rational64(model, &node, &num, &den) < 0)
      {
        throw InternalSolverException(take_yices_error());
      }
      if (den != 1)
      {
        throw NotImplementedException(
            "Yices gave the non-integer array model value "
            + std::to_string(num) + "/" + std::to_string(den));
      }
      return solver.make_term(std::to_string(num), sort, 10);
    }
    case YVAL_UNKNOWN:
    case YVAL_ALGEBRAIC:
#if __YICES_VERSION > 2 || __YICES_VERSION_MAJOR >= 7
    case YVAL_FINITEFIELD:
#endif
    case YVAL_SCALAR:
    case YVAL_TUPLE:
    case YVAL_FUNCTION:
    case YVAL_MAPPING: break;
  }
  throw NotImplementedException(
      "Yices gave an array model node of tag " + std::to_string(node.node_tag)
      + ", which this backend cannot turn back into a term");
}

UnorderedTermMap Yices2Solver::get_array_values(const Term & arr,
                                                Term & out_const_base) const
{
  out_const_base = nullptr;
  shared_ptr<Yices2Term> yarr = backend_pointer_cast<Yices2Term>(arr);
  Sort arrsort = arr->get_sort();
  Sort idxsort = arrsort->get_indexsort();
  Sort elemsort = arrsort->get_elemsort();
  model_t * model = ctx ? yices_get_model(ctx.get(), true) : nullptr;
  if (!model)
  {
    yices_clear_error();
    throw IncorrectUsageException(
        "Last call to check_sat was not sat, cannot get a model.");
  }

  // A constant array is a lambda, which Yices' model can apply but not
  // evaluate on its own: asking gives "can't evaluate lambdas". Reading an
  // index out of one does work, so get_value is the way to a constant
  // array's contents.
  if (arr->is_value())
  {
    throw NotImplementedException(
        "Yices2 cannot give the model of a constant array, which it writes "
        "as a lambda and will not evaluate; read an index with get_value "
        "instead");
  }

  // Yices models an array as a function: one default value, plus a mapping
  // for each index that differs from it. The default is the constant base.
  yval_t node;
  if (yices_get_value(model, yarr->term, &node) < 0)
  {
    throw InternalSolverException(take_yices_error());
  }
  if (yices_val_function_arity(model, &node) != 1)
  {
    throw NotImplementedException(
        "Yices gave an array model of arity other than one");
  }

  yval_t def;
  yval_vector_t mappings;
  yices_init_yval_vector(&mappings);
  if (yices_val_expand_function(model, &node, &def, &mappings) < 0)
  {
    yices_delete_yval_vector(&mappings);
    throw InternalSolverException(take_yices_error());
  }

  UnorderedTermMap assignments;
  try
  {
    out_const_base = term_from_yval(*this, model, def, elemsort);
    for (uint32_t m = 0; m < mappings.size; m++)
    {
      yval_t index;
      yval_t value;
      if (yices_val_expand_mapping(model, &mappings.data[m], &index, &value)
          < 0)
      {
        throw InternalSolverException(take_yices_error());
      }
      assignments[term_from_yval(*this, model, index, idxsort)] =
          term_from_yval(*this, model, value, elemsort);
    }
  }
  catch (...)
  {
    yices_delete_yval_vector(&mappings);
    throw;
  }
  yices_delete_yval_vector(&mappings);
  return assignments;
}

void Yices2Solver::get_unsat_assumptions(UnorderedTermSet & out) const
{
  if (!ctx)
  {
    throw IncorrectUsageException(
        "Last call to check_sat was not unsat, cannot get unsat core.");
  }
  term_vector_t ycore;
  yices_init_term_vector(&ycore);
  int32_t err_code = yices_get_unsat_core(ctx.get(), &ycore);
  // yices2 documentation: returns -1 if ctx status was not UNSAT
  if (err_code == -1)
  {
    throw IncorrectUsageException(
        "Last call to check_sat was not unsat, cannot get unsat core.");
  }

  for (size_t i = 0; i < ycore.size; ++i)
  {
    if (!ycore.data[i])
    {
      throw InternalSolverException("Got an empty term from vector");
    }
    out.insert(std::make_shared<Yices2Term>(ycore.data[i]));
  }

  yices_delete_term_vector(&ycore);
}

Sort Yices2Solver::make_sort(const std::string name, uint64_t arity) const
{
  type_t y_sort;

  if (!arity)
  {
    y_sort = yices_new_uninterpreted_type();
    yices_set_type_name(y_sort, name.c_str());
  }
  else
  {
    throw NotImplementedException(
        "Yices does not support uninterpreted type with non-zero arity.");
  }

  if (yices_error_code() != 0)
  {
    throw InternalSolverException(take_yices_error());
  }

  return std::make_shared<Yices2Sort>(y_sort);
}

Sort Yices2Solver::make_sort(SortKind sk) const
{
  type_t y_sort;

  if (sk == BOOL)
  {
    y_sort = yices_bool_type();
  }
  else if (sk == INT)
  {
    y_sort = yices_int_type();
  }
  else if (sk == REAL)
  {
    y_sort = yices_real_type();
  }
  else
  {
    std::string msg("Can't create sort with sort constructor ");
    msg += to_string(sk);
    msg += " and no arguments";
    throw IncorrectUsageException(msg.c_str());
  }

  if (yices_error_code() != 0)
  {
    throw InternalSolverException(take_yices_error());
  }

  return std::make_shared<Yices2Sort>(y_sort);
}

Sort Yices2Solver::make_sort(SortKind sk, uint64_t size) const
{
  type_t y_sort;

  if (sk == BV)
  {
    y_sort = yices_bv_type(narrow_width(size));
  }
  else
  {
    std::string msg("Can't create sort with sort constructor ");
    msg += to_string(sk);
    msg += " and an integer argument";
    throw IncorrectUsageException(msg.c_str());
  }

  if (yices_error_code() != 0)
  {
    throw InternalSolverException(take_yices_error());
  }

  return std::make_shared<Yices2Sort>(y_sort);
}

Sort Yices2Solver::make_sort(SortKind sk, const SortVec & sorts) const
{
  type_t y_sort;

  if (sk == FUNCTION)
  {
    if (sorts.size() < 2)
    {
      throw IncorrectUsageException(
          "Function sort must have >=2 sort arguments.");
    }

    // arity is one less, because last sort is return sort
    uint32_t arity = narrow_num_args(sorts.size() - 1);

    std::vector<type_t> ysorts;

    ysorts.reserve(arity);

    type_t ys;
    for (uint32_t i = 0; i < arity; i++)
    {
      ys = backend_pointer_cast<Yices2Sort>(sorts[i])->type;
      ysorts.push_back(ys);
    }

    Sort sort = sorts.back();
    ys = backend_pointer_cast<Yices2Sort>(sort)->type;

    y_sort = yices_function_type(arity, ysorts.data(), ys);
  }
  else if (sk == ARRAY && sorts.size() == 2)
  {
    std::shared_ptr<Yices2Sort> s1 = backend_pointer_cast<Yices2Sort>(sorts[0]);
    std::shared_ptr<Yices2Sort> s2 = backend_pointer_cast<Yices2Sort>(sorts[1]);
    y_sort = yices_function_type1(s1->type, s2->type);
  }
  else
  {
    std::string msg("Can't create sort from sort constructor ");
    msg += to_string(sk);
    msg += " with a vector of sorts of size " + std::to_string(sorts.size());
    throw IncorrectUsageException(msg.c_str());
  }

  if (yices_error_code() != 0)
  {
    throw InternalSolverException(take_yices_error());
  }

  return std::make_shared<Yices2Sort>(y_sort, sk == FUNCTION);
}

Term Yices2Solver::make_symbol(const std::string name, const Sort & sort)
{
  if (symbol_table.find(name) != symbol_table.end())
  {
    throw IncorrectUsageException("symbol " + name + " has already been used.");
  }

  shared_ptr<Yices2Sort> ysort = backend_pointer_cast<Yices2Sort>(sort);
  term_t y_term = yices_new_uninterpreted_term(ysort->type);
  yices_set_term_name(y_term, name.c_str());

  if (ysort->get_sort_kind() == FUNCTION)
  {
    Yices2InstanceRef::mark_function(y_term);
  }
  Term sym = std::make_shared<Yices2Term>(y_term);
  assert(sym);
  symbol_table[name] = sym;
  return sym;
}

Term Yices2Solver::get_symbol(const std::string & name) const
{
  auto it = symbol_table.find(name);
  if (it == symbol_table.end())
  {
    throw IncorrectUsageException("Symbol named " + name + " does not exist.");
  }
  return it->second;
}

Term Yices2Solver::make_param(const std::string name, const Sort & sort) const
{
  shared_ptr<Yices2Sort> ysort = backend_pointer_cast<Yices2Sort>(sort);
  // a variable, not an uninterpreted term: this is the one a quantifier can
  // bind, and the only one yices_forall and yices_lambda accept
  term_t y_term = yices_new_variable(ysort->type);
  yices_set_term_name(y_term, name.c_str());
  return std::make_shared<Yices2Term>(y_term);
}

/**
 * The Int constant a bit-vector constant stands for, read as unsigned or as
 * two's complement
 */
static term_t bv_value_to_int(term_t bv_value, bool is_signed)
{
  const uint32_t width = yices_term_bitsize(bv_value);
  // yices gives the bits least significant first
  vector<int32_t> bits(width);
  yices_bv_const_value(bv_value, bits.data());
  mpz_t value;
  mpz_init(value);
  for (uint32_t i = 0; i < width; ++i)
  {
    if (bits[i])
    {
      mpz_setbit(value, i);
    }
  }
  if (is_signed && bits[width - 1])
  {
    mpz_t modulus;
    mpz_init(modulus);
    mpz_setbit(modulus, width);
    mpz_sub(value, value, modulus);
    mpz_clear(modulus);
  }
  term_t res = yices_mpz(value);
  mpz_clear(value);
  return res;
}

/**
 * The exponent of a Pow, which yices_power takes as a uint32_t, so only a
 * constant non-negative integer that fits in one
 */
static uint32_t pow_exponent(term_t term)
{
  bool fits = false;
  uint32_t res = 0;
  // checked first, as yices_rational_const_value fails on anything else
  if (yices_term_constructor(term) == YICES_ARITH_CONSTANT)
  {
    mpq_t value;
    mpq_init(value);
    yices_rational_const_value(term, value);
    if (mpz_cmp_ui(mpq_denref(value), 1) == 0 && mpz_sgn(mpq_numref(value)) >= 0
        && mpz_cmp_ui(mpq_numref(value), UINT32_MAX) <= 0)
    {
      fits = true;
      res = static_cast<uint32_t>(mpz_get_ui(mpq_numref(value)));
    }
    mpq_clear(value);
  }
  if (!fits)
  {
    throw NotImplementedException(
        "Yices2 can only raise to a constant integer exponent from 0 to "
        + std::to_string(UINT32_MAX));
  }
  return res;
}

/** Refuses po applied to num_args arguments, which Yices2 has no operator for
 *  @throws IncorrectUsageException where SMT-LIB does not allow that many
 *          arguments
 *  @throws NotImplementedException otherwise
 */
[[noreturn]] static void throw_unsupported(PrimOp po, size_t num_args)
{
  const pair<size_t, size_t> arity = get_arity(po);
  if (num_args < arity.first || num_args > arity.second)
  {
    throw IncorrectUsageException("Can't apply " + to_string(po) + " to "
                                  + std::to_string(num_args)
                                  + (num_args == 1 ? " term" : " terms"));
  }
  throw NotImplementedException("Yices2 does not support the operator "
                                + to_string(po));
}

/** The term of op applied to one argument
 *  @throws as throw_unsupported where Yices2 has no such op
 */
static term_t unary_term(const Op & op, term_t a)
{
  switch (op.prim_op)
  {
    case Not: return yices_not(a);
    case Negate: return yices_neg(a);
    case Abs: return yices_abs(a);
    case To_Real:
      if (!yices_term_is_arithmetic(a))
      {
        throw IncorrectUsageException(
            "Can't apply to_real to a non-arithmetic term");
      }
      // Int is a subtype of Real in Yices2, which has no conversion
      return a;
    case To_Int: return yices_floor(a);
    case Is_Int: return yices_is_int_atom(a);
    case Divisible:
      if (op.indices[0] < 1)
      {
        throw IncorrectUsageException("Can't create divisible with index < 1");
      }
      return yices_divides_atom(
          yices_parse_rational(std::to_string(op.indices[0]).c_str()), a);
    case Extract:
      return yices_bvextract(
          a, narrow_index(op, op.indices[1]), narrow_index(op, op.indices[0]));
    case BVNot: return yices_bvnot(a);
    case BVNeg: return yices_bvneg(a);
    case Zero_Extend:
      return yices_zero_extend(a, narrow_index(op, op.indices[0]));
    case Sign_Extend:
      return yices_sign_extend(a, narrow_index(op, op.indices[0]));
    case Repeat:
      if (op.indices[0] < 1)
      {
        throw IncorrectUsageException("Can't create repeat with index < 1");
      }
      return yices_bvrepeat(a, narrow_index(op, op.indices[0]));
    case Rotate_Left:
      return yices_rotate_left(a, narrow_index(op, op.indices[0]));
    case Rotate_Right:
      return yices_rotate_right(a, narrow_index(op, op.indices[0]));
    case BV_To_Nat:
    case UBV_To_Int:
    case SBV_To_Int:
      if (!yices_term_is_bitvector(a))
      {
        throw IncorrectUsageException("Can't apply " + op.to_string()
                                      + " to a non-bit-vector term");
      }
      // Yices2 has no conversion, so only a value can be folded into one
      if (yices_term_constructor(a) != YICES_BV_CONSTANT)
      {
        throw NotImplementedException("Yices2 has no " + op.to_string()
                                      + ", so it can only apply it to a "
                                        "bit-vector value");
      }
      return bv_value_to_int(a, op.prim_op == SBV_To_Int);
    case Int_To_BV: {
      if (!yices_term_is_int(a))
      {
        throw IncorrectUsageException(
            "Can't apply int_to_bv to a non-integer term");
      }
      // Yices2 has no conversion, so only a value can be folded into one
      if (yices_term_constructor(a) != YICES_ARITH_CONSTANT)
      {
        throw NotImplementedException(
            "Yices2 has no int_to_bv, so it can only apply it to an Int value");
      }
      const uint32_t width = narrow_index(op, op.indices[0]);
      mpq_t value;
      mpq_init(value);
      yices_rational_const_value(a, value);
      // truncates two's complement to the width, which is the value mod
      // 2^width
      const term_t res = yices_bvconst_mpz(width, mpq_numref(value));
      mpq_clear(value);
      return res;
    }
    default: throw_unsupported(op.prim_op, 1);
  }
}

/** The term of po applied to two arguments
 *  @throws as throw_unsupported where Yices2 has no such op
 */
static term_t binary_term(PrimOp po, term_t a, term_t b)
{
  switch (po)
  {
    case And: return yices_and2(a, b);
    case Or: return yices_or2(a, b);
    case Xor: return yices_xor2(a, b);
    case Implies: return yices_implies(a, b);
    case Equal: return yices_eq(a, b);
    case Distinct:
      return yices_distinct(2, std::array<term_t, 2>{ { a, b } }.data());
    case Plus: return yices_add(a, b);
    case Minus: return yices_sub(a, b);
    case Mult: return yices_mul(a, b);
    case Div: return yices_division(a, b);
    case Lt: return yices_arith_lt_atom(a, b);
    case Le: return yices_arith_leq_atom(a, b);
    case Gt: return yices_arith_gt_atom(a, b);
    case Ge: return yices_arith_geq_atom(a, b);
    case Mod: return yices_imod(a, b);
    case Pow: return yices_power(a, pow_exponent(b));
    case IntDiv: return yices_idiv(a, b);
    case Concat: return yices_bvconcat2(a, b);
    case BVAnd: return yices_bvand2(a, b);
    case BVOr: return yices_bvor2(a, b);
    case BVXor: return yices_bvxor2(a, b);
    case BVNand: return yices_bvnand(a, b);
    case BVNor: return yices_bvnor(a, b);
    case BVXnor: return yices_bvxnor(a, b);
    case BVAdd: return yices_bvadd(a, b);
    case BVSub: return yices_bvsub(a, b);
    case BVMul: return yices_bvmul(a, b);
    case BVUdiv: return yices_bvdiv(a, b);
    case BVSdiv: return yices_bvsdiv(a, b);
    case BVUrem: return yices_bvrem(a, b);
    case BVSrem: return yices_bvsrem(a, b);
    case BVSmod: return yices_bvsmod(a, b);
    case BVShl: return yices_bvshl(a, b);
    case BVAshr: return yices_bvashr(a, b);
    case BVLshr: return yices_bvlshr(a, b);
    case BVComp: return ext_yices_bvcomp(a, b);
    case BVUlt: return yices_bvlt_atom(a, b);
    case BVUle: return yices_bvle_atom(a, b);
    case BVUgt: return yices_bvgt_atom(a, b);
    case BVUge: return yices_bvge_atom(a, b);
    case BVSlt: return yices_bvslt_atom(a, b);
    case BVSle: return yices_bvsle_atom(a, b);
    case BVSgt: return yices_bvsgt_atom(a, b);
    case BVSge: return yices_bvsge_atom(a, b);
    case Select: return ext_yices_select(a, b);
    default: throw_unsupported(po, 2);
  }
}

/** The term of op applied to terms, three or more, whose Yices2 terms are
 *  args, in a single Yices2 call where Yices2 has one and through
 *  make_nary_term otherwise
 *
 *  Some of the calls may modify args.
 */
static Term variadic_term(const AbsSmtSolver * solver,
                          const Op & op,
                          const TermVec & terms,
                          vector<term_t> & args)
{
  const uint32_t n = narrow_num_args(args.size());
  term_t * a = args.data();
  term_t res;
  switch (op.prim_op)
  {
    case And:
      res = n == 3 ? yices_and3(a[0], a[1], a[2]) : yices_and(n, a);
      break;
    case Or: res = n == 3 ? yices_or3(a[0], a[1], a[2]) : yices_or(n, a); break;
    case Xor:
      res = n == 3 ? yices_xor3(a[0], a[1], a[2]) : yices_xor(n, a);
      break;
    case Distinct: res = yices_distinct(n, a); break;
    case Plus: res = yices_sum(n, a); break;
    case Mult: res = yices_product(n, a); break;
    case BVAnd:
      res = n == 3 ? yices_bvand3(a[0], a[1], a[2]) : yices_bvand(n, a);
      break;
    case BVOr:
      res = n == 3 ? yices_bvor3(a[0], a[1], a[2]) : yices_bvor(n, a);
      break;
    case BVXor:
      res = n == 3 ? ext_yices_bvxor3(a[0], a[1], a[2]) : yices_bvxor(n, a);
      break;
    case BVAdd: res = yices_bvsum(n, a); break;
    case BVMul: res = yices_bvproduct(n, a); break;
    default: return make_nary_term(solver, op, terms);
  }
  return checked_term(res);
}

Term Yices2Solver::make_term(Op op, const TermVec & terms) const
{
  size_t size = terms.size();
  if (!size)
  {
    string msg("Can't apply ");
    msg += op.to_string();
    msg += " to zero terms.";
    throw IncorrectUsageException(msg);
  }

  vector<term_t> yterms;
  yterms.reserve(size);
  for (const auto & t : terms)
  {
    yterms.push_back(backend_pointer_cast<Yices2Term>(t)->term);
  }

  term_t res;
  if (size == 1)
  {
    res = unary_term(op, yterms[0]);
  }
  else if (op.prim_op == Forall || op.prim_op == Exists)
  {
    // Yices2 has quantifiers, but this backend does not build them yet
    throw NotImplementedException("The Yices2 backend does not support "
                                  + to_string(op.prim_op));
  }
  else if (op.prim_op == Apply)
  {
    if (!yices_term_is_function(yterms[0]))
    {
      string msg(
          "Expecting an uninterpreted function to be used with Apply but got ");
      msg += terms[0]->to_string();
      throw IncorrectUsageException(msg);
    }
    // the first term is the function, applied to the rest
    res = yices_application(
        yterms[0], narrow_num_args(size - 1), yterms.data() + 1);
  }
  else if (size == 2)
  {
    res = binary_term(op.prim_op, yterms[0], yterms[1]);
  }
  else if (size == 3 && op.prim_op == Ite)
  {
    res = yices_ite(yterms[0], yterms[1], yterms[2]);
  }
  else if (size == 3 && op.prim_op == Store)
  {
    res = ext_yices_store(yterms[0], yterms[1], yterms[2]);
  }
  else
  {
    return variadic_term(this, op, terms, yterms);
  }

  return checked_term(res);
}

void Yices2Solver::do_reset()
{
  // only this solver's own state: yices_reset would delete the terms,
  // contexts and configurations of every other solver too
  ctx.reset();
  yices_free_config(config);
  config = yices_new_config();
  symbol_table.clear();
  pushes_after_unsat = 0;
  time_limit = 0;
  logic_ = "ALL";
  assertions.clear();
  scope_starts.clear();
}

void Yices2Solver::do_reset_assertions()
{
  if (ctx)
  {
    yices_reset_context(ctx.get());
  }
  pushes_after_unsat = 0;
  assertions.clear();
  scope_starts.clear();
}

void Yices2Solver::dump_smt2(std::string filename) const
{
  std::ofstream out(filename);
  smtlib_benchmark(out, logic_, assertions);
}

Term Yices2Solver::substitute(const Term term,
                              const UnorderedTermMap & substitution_map) const
{
  shared_ptr<Yices2Term> yterm = backend_pointer_cast<Yices2Term>(term);

  vector<term_t> to_subst;
  vector<term_t> values;

  shared_ptr<Yices2Term> tmp_key;
  shared_ptr<Yices2Term> tmp_val;

  for (auto elem : substitution_map)
  {
    tmp_key = backend_pointer_cast<Yices2Term>(elem.first);

    to_subst.push_back(tmp_key->term);
    tmp_val = backend_pointer_cast<Yices2Term>(elem.second);

    values.push_back(tmp_val->term);
  }

  term_t res = yices_subst_term(
      detail::narrow<uint32_t>(to_subst.size(), "a number of substitutions"),
      to_subst.data(),
      values.data(),
      yterm->term);

  return checked_term(res);
}

// helpers
void Yices2Solver::timelimit_start()
{
  if (time_limit)
  {
    signal(SIGALRM, yices2_timelimit_handler);
    assert(running_ctx == nullptr);
    assert(!yices2_terminated);
    running_ctx = get_context().get();
    itimerval timer{};
    timer.it_value.tv_sec = static_cast<time_t>(time_limit);
    timer.it_value.tv_usec = static_cast<suseconds_t>(
        (time_limit - static_cast<double>(timer.it_value.tv_sec)) * 1e6);
    setitimer(ITIMER_REAL, &timer, nullptr);
  }
}

bool Yices2Solver::timelimit_end()
{
  bool res = false;
  if (time_limit)
  {
    // Cancel first: clearing running_ctx before the timer is off leaves a
    // window where the handler runs against a null context.
    itimerval disarm{};
    setitimer(ITIMER_REAL, &disarm, nullptr);
    res |= yices2_terminated != 0;
    yices2_terminated = 0;
    running_ctx = nullptr;
  }
  return res;
}

/* end Yices2Solver implementation */

}  // namespace smt
