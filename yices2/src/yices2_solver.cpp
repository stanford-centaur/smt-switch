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

#include <signal.h>
#include <sys/time.h>

#include <cassert>
#include <cstdint>
#include <string>

#include "solver_utils.h"
#include "yices.h"
#include "yices2_extensions.h"

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

/* Yices2 Op mappings */
typedef term_t (*yices_un_fun)(term_t);
typedef term_t (*yices_bin_fun)(term_t, term_t);
typedef term_t (*yices_tern_fun)(term_t, term_t, term_t);
typedef term_t (*yices_variadic_fun)(uint32_t, term_t[]);

// TODO's:
// Pretty sure not implemented in Yices.
// Good candidates for extension.
//  To_Real,
//  BVComp,
//  BV_To_Nat,

// Arrays are represented as functions in Yices.
// I don't think const_array can be supported,
// unless we use Yices lambdas.
// Const_Array,

const unordered_map<PrimOp, yices_un_fun> yices_unary_ops(
    { { Not, yices_not },
      { Negate, yices_neg },
      { Abs, yices_abs },
      { To_Int, yices_floor },
      { Is_Int, yices_is_int_atom },
      { BVNot, yices_bvnot },
      { BVNeg, yices_bvneg } });

const unordered_map<PrimOp, yices_bin_fun> yices_binary_ops(
    { { And, yices_and2 },           { Or, yices_or2 },
      { Xor, yices_xor2 },           { Implies, yices_implies },
      { Plus, yices_add },           { Minus, yices_sub },
      { Mult, yices_mul },           { Div, yices_division },
      { Lt, yices_arith_lt_atom },   { IntDiv, yices_idiv },
      { Le, yices_arith_leq_atom },  { Gt, yices_arith_gt_atom },
      { Ge, yices_arith_geq_atom },  { Equal, yices_eq },
      { Mod, yices_imod },           { Concat, yices_bvconcat2 },
      { BVAnd, yices_bvand2 },       { BVOr, yices_bvor2 },
      { BVXor, yices_bvxor2 },       { BVNand, yices_bvnand },
      { BVNor, yices_bvnor },        { BVXnor, yices_bvxnor },
      { BVAdd, yices_bvadd },        { BVSub, yices_bvsub },
      { BVMul, yices_bvmul },        { BVUdiv, yices_bvdiv },
      { BVUrem, yices_bvrem },       { BVSdiv, yices_bvsdiv },
      { BVSrem, yices_bvsrem },      { BVSmod, yices_bvsmod },
      { BVShl, yices_bvshl },        { BVAshr, yices_bvashr },
      { BVLshr, yices_bvlshr },      { BVUlt, yices_bvlt_atom },
      { BVUle, yices_bvle_atom },    { BVUgt, yices_bvgt_atom },
      { BVUge, yices_bvge_atom },    { BVSle, yices_bvsle_atom },
      { BVSlt, yices_bvslt_atom },   { BVSge, yices_bvsge_atom },
      { BVSgt, yices_bvsgt_atom },   { Select, ext_yices_select },
      { Apply, yices_application1 }, { BVComp, ext_yices_bvcomp } });

const unordered_map<PrimOp, yices_tern_fun> yices_ternary_ops(
    { { And, yices_and3 },
      { Or, yices_or3 },
      { Xor, yices_xor3 },
      { Ite, yices_ite },
      { BVAnd, yices_bvand3 },
      { BVOr, yices_bvor3 },
      { BVXor, yices_bvxor3 },
      { Apply, yices_application2 },
      { Store, ext_yices_store } });

const unordered_map<PrimOp, yices_variadic_fun> yices_variadic_ops({
    { And, yices_and },
    { Or, yices_or },
    { Xor, yices_xor },
    { Distinct, yices_distinct }
    // { BVAnd, yices_bvand } has different format.
});

/* Yices2Solver implementation */

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
          "Yices2 can only set incremental before the first assertion or "
          "check");
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
    ;
    ;
  }
  else
  {
    string msg("Option ");
    msg += option;
    msg += " is not yet supported for the Yices2 backend";
    throw NotImplementedException(msg);
  }
}

/**
 * Yices' description of its last error, freeing the string it returns and
 * clearing the error, which later calls would otherwise report again
 */
static std::string take_yices_error()
{
  char * reason = yices_error_string();
  std::string msg(reason);
  yices_free_string(reason);
  yices_clear_error();
  return msg;
}

void Yices2Solver::set_logic(const std::string logic)
{
  if (ctx)
  {
    throw IncorrectUsageException(
        "Yices2 can only set the logic before the first assertion or check");
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
}

context_t * Yices2Solver::get_context() const
{
  if (!ctx)
  {
    ctx = yices_new_context(config);
    if (!ctx)
    {
      throw IncorrectUsageException(
          "Yices2 cannot create a context with the logic and options set: "
          + take_yices_error());
    }
  }
  return ctx;
}

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

  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }

  return std::make_shared<Yices2Term>(y_term);
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
    y_term = yices_bvconst_int64(sort->get_width(), i);
  }
  else
  {
    string msg("Can't create value ");
    msg += i;
    msg += " with sort ";
    msg += sort->to_string();
    throw IncorrectUsageException(msg);
  }

  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }

  return std::make_shared<Yices2Term>(y_term);
}

Term Yices2Solver::make_term(const std::string val,
                             const Sort & sort,
                             uint64_t base) const
{
  term_t y_term;

  SortKind sk = sort->get_sort_kind();
  if (sk == BV)
  {
    y_term = ext_yices_make_bv_number(val.c_str(), sort->get_width(), base);
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

  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }

  return std::make_shared<Yices2Term>(y_term);
}

Term Yices2Solver::make_term(const Term & val, const Sort & sort) const
{
  throw NotImplementedException(
      "Constant arrays not supported for Yices2 backend.");
}

void Yices2Solver::assert_formula(const Term & t)
{
  shared_ptr<Yices2Term> yterm = static_pointer_cast<Yices2Term>(t);
  if (!yices_type_is_bool(yices_type_of_term(yterm->term)))
  {
    throw IncorrectUsageException("Attempted to assert non-boolean to solver: "
                                  + t->to_string());
  }

  yices_assert_formula(get_context(), yterm->term);
  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }
}

Result Yices2Solver::check_sat()
{
  timelimit_start();
  smt_status_t res = yices_check_context(get_context(), NULL);
  bool tl_triggered = timelimit_end();

  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
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

Result Yices2Solver::check_sat_assuming(const TermVec & assumptions)
{
  vector<term_t> y_assumps;
  y_assumps.reserve(assumptions.size());

  shared_ptr<Yices2Term> ya;
  for (auto a : assumptions)
  {
    ya = static_pointer_cast<Yices2Term>(a);
    y_assumps.push_back(ya->term);
  }

  return check_sat_assuming(y_assumps);
}

void Yices2Solver::push(uint64_t num)
{
  if (yices_context_status(get_context()) == YICES_STATUS_UNSAT)
  {
    pushes_after_unsat += num;
    return;
  }

  for (size_t i = 0; i < num; ++i)
  {
    yices_push(get_context());
  }

  context_level += num;
}

void Yices2Solver::pop(uint64_t num)
{
  for (size_t i = 0; i < num; ++i)
  {
    if (pushes_after_unsat)
    {
      pushes_after_unsat--;
      continue;
    }
    yices_pop(get_context());
  }

  context_level -= num;
}

uint64_t Yices2Solver::get_context_level() const { return context_level; }

Term Yices2Solver::get_value(const Term & t) const
{
  shared_ptr<Yices2Term> yterm = static_pointer_cast<Yices2Term>(t);
  model_t * model = yices_get_model(get_context(), true);

  if (!yices_term_is_function(yterm->term))
  {
    return std::make_shared<Yices2Term>(
        yices_get_value_as_term(model, yterm->term));
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
        throw InternalSolverException(yices_error_string());
      }
      return solver.make_term(b != 0);
    }
    case YVAL_BV: {
      uint32_t width = yices_val_bitsize(model, &node);
      std::vector<int32_t> bits(width);
      if (yices_val_get_bv(model, &node, bits.data()) < 0)
      {
        throw InternalSolverException(yices_error_string());
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
        throw InternalSolverException(yices_error_string());
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
    case YVAL_FINITEFIELD:
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
  shared_ptr<Yices2Term> yarr = static_pointer_cast<Yices2Term>(arr);
  Sort arrsort = arr->get_sort();
  Sort idxsort = arrsort->get_indexsort();
  Sort elemsort = arrsort->get_elemsort();
  model_t * model = yices_get_model(get_context(), true);

  // Yices models an array as a function: one default value, plus a mapping
  // for each index that differs from it. The default is the constant base.
  yval_t node;
  if (yices_get_value(model, yarr->term, &node) < 0)
  {
    throw InternalSolverException(yices_error_string());
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
    throw InternalSolverException(yices_error_string());
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
        throw InternalSolverException(yices_error_string());
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

void Yices2Solver::get_unsat_assumptions(UnorderedTermSet & out)
{
  term_vector_t ycore;
  yices_init_term_vector(&ycore);
  int32_t err_code = yices_get_unsat_core(get_context(), &ycore);
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
    std::string msg(yices_error_string());

    throw InternalSolverException(msg.c_str());
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
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }

  return std::make_shared<Yices2Sort>(y_sort);
}

Sort Yices2Solver::make_sort(SortKind sk, uint64_t size) const
{
  type_t y_sort;

  if (sk == BV)
  {
    y_sort = yices_bv_type(size);
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
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
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
    uint32_t arity = sorts.size() - 1;

    std::vector<type_t> ysorts;

    ysorts.reserve(arity);

    type_t ys;
    for (uint32_t i = 0; i < arity; i++)
    {
      ys = std::static_pointer_cast<Yices2Sort>(sorts[i])->type;
      ysorts.push_back(ys);
    }

    Sort sort = sorts.back();
    ys = std::static_pointer_cast<Yices2Sort>(sort)->type;

    y_sort = yices_function_type(arity, &ysorts[0], ys);
  }
  else if (sk == ARRAY && sorts.size() == 2)
  {
    std::shared_ptr<Yices2Sort> s1 =
        std::static_pointer_cast<Yices2Sort>(sorts[0]);
    std::shared_ptr<Yices2Sort> s2 =
        std::static_pointer_cast<Yices2Sort>(sorts[1]);
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
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }

  return std::make_shared<Yices2Sort>(y_sort, sk == FUNCTION);
}

Term Yices2Solver::make_symbol(const std::string name, const Sort & sort)
{
  if (symbol_table.find(name) != symbol_table.end())
  {
    throw IncorrectUsageException("symbol " + name + " has already been used.");
  }

  shared_ptr<Yices2Sort> ysort = static_pointer_cast<Yices2Sort>(sort);
  term_t y_term = yices_new_uninterpreted_term(ysort->type);
  yices_set_term_name(y_term, name.c_str());

  Term sym;
  if (ysort->get_sort_kind() == FUNCTION)
  {
    sym = std::make_shared<Yices2Term>(y_term, true);
  }
  else
  {
    sym = std::make_shared<Yices2Term>(y_term);
  }
  assert(sym);
  symbol_table[name] = sym;
  return sym;
}

Term Yices2Solver::get_symbol(const std::string & name)
{
  auto it = symbol_table.find(name);
  if (it == symbol_table.end())
  {
    throw IncorrectUsageException("Symbol named " + name + " does not exist.");
  }
  return it->second;
}

Term Yices2Solver::make_param(const std::string name, const Sort & sort)
{
  shared_ptr<Yices2Sort> ysort = static_pointer_cast<Yices2Sort>(sort);
  // a variable, not an uninterpreted term: this is the one a quantifier can
  // bind, and the only one yices_forall and yices_lambda accept
  term_t y_term = yices_new_variable(ysort->type);
  yices_set_term_name(y_term, name.c_str());
  return std::make_shared<Yices2Term>(y_term);
}

Term Yices2Solver::make_term(Op op, const Term & t) const
{
  shared_ptr<Yices2Term> yterm = static_pointer_cast<Yices2Term>(t);
  term_t res;

  if (op.prim_op == Extract)
  {
    res = yices_bvextract(
        yterm->term, narrow_index(op, op.idx1), narrow_index(op, op.idx0));
  }
  else if (op.prim_op == Zero_Extend)
  {
    res = yices_zero_extend(yterm->term, narrow_index(op, op.idx0));
  }
  else if (op.prim_op == Sign_Extend)
  {
    res = yices_sign_extend(yterm->term, narrow_index(op, op.idx0));
  }
  else if (op.prim_op == Repeat)
  {
    if (op.num_idx < 1)
    {
      throw IncorrectUsageException("Can't create repeat with index < 1");
    }
    res = yices_bvrepeat(yterm->term, narrow_index(op, op.idx0));
  }
  else if (op.prim_op == Rotate_Left)
  {
    res = yices_rotate_left(yterm->term, narrow_index(op, op.idx0));
  }
  else if (op.prim_op == Rotate_Right)
  {
    res = yices_rotate_right(yterm->term, narrow_index(op, op.idx0));
  }
  else if (op.prim_op == Int_To_BV)
  {
    res = yices_bvconst_int64(yterm->term, op.idx0);
  }
  else if (!op.num_idx)
  {
    if (yices_unary_ops.find(op.prim_op) != yices_unary_ops.end())
    {
      res = yices_unary_ops.at(op.prim_op)(yterm->term);
    }
    else
    {
      string msg("Can't apply ");
      msg += op.to_string();
      msg += " to the term or not supported by Yices2 backend yet.";
      throw IncorrectUsageException(msg);
    }
  }
  else
  {
    string msg = op.to_string();
    msg += " not supported for one term argument";
    throw IncorrectUsageException(msg);
  }

  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }

  return std::make_shared<Yices2Term>(res);
}

Term Yices2Solver::make_term(Op op, const Term & t0, const Term & t1) const
{
  shared_ptr<Yices2Term> yterm0 = static_pointer_cast<Yices2Term>(t0);
  shared_ptr<Yices2Term> yterm1 = static_pointer_cast<Yices2Term>(t1);
  term_t res;
  if (!op.num_idx)
  {
    if (yices_binary_ops.find(op.prim_op) != yices_binary_ops.end())
    {
      res = yices_binary_ops.at(op.prim_op)(yterm0->term, yterm1->term);
    }
    else if (yices_variadic_ops.find(op.prim_op) != yices_variadic_ops.end())
    {
      term_t terms[2] = { yterm0->term, yterm1->term };
      res = yices_variadic_ops.at(op.prim_op)(2, terms);
    }
    else if (op.prim_op == Pow)
    {
      res = yices_power(yterm0->term, (t1->to_int()));
    }
    else
    {
      string msg("Can't apply ");
      msg += op.to_string();
      msg += " to two terms, or not supported by Yices2 backend yet.";
      throw IncorrectUsageException(msg);
    }
  }
  else
  {
    string msg = op.to_string();
    msg += " not supported for two term arguments";
    throw IncorrectUsageException(msg);
  }

  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());

    throw InternalSolverException(msg.c_str());
  }

  if (yices_term_is_function(yterm0->term) && op.prim_op == Apply)
  {
    return std::make_shared<Yices2Term>(res, true);
  }
  else
  {
    return std::make_shared<Yices2Term>(res);
  }
}

Term Yices2Solver::make_term(Op op,
                             const Term & t0,
                             const Term & t1,
                             const Term & t2) const
{
  shared_ptr<Yices2Term> yterm0 = static_pointer_cast<Yices2Term>(t0);
  shared_ptr<Yices2Term> yterm1 = static_pointer_cast<Yices2Term>(t1);
  shared_ptr<Yices2Term> yterm2 = static_pointer_cast<Yices2Term>(t2);
  term_t res;
  if (!op.num_idx)
  {
    if (yices_ternary_ops.find(op.prim_op) != yices_ternary_ops.end())
    {
      res = yices_ternary_ops.at(op.prim_op)(
          yterm0->term, yterm1->term, yterm2->term);
    }
    else if (yices_variadic_ops.find(op.prim_op) != yices_variadic_ops.end())
    {
      term_t terms[3] = { yterm0->term, yterm1->term, yterm2->term };
      res = yices_variadic_ops.at(op.prim_op)(3, terms);
    }
    // TODO: Threw this is for term traversal, but it's not a fix.
    // Need to handle all "variadic" Ops this way with proper L/R association.
    else if (op.prim_op == Plus)
    {
      res = yices_add(yterm0->term, yices_add(yterm1->term, yterm2->term));
    }
    else
    {
      string msg("Can't apply ");
      msg += op.to_string();
      msg += " to three terms, or not supported by Yices2 backend yet.";
      throw IncorrectUsageException(msg);
    }
  }
  else
  {
    string msg = op.to_string();
    msg += " not supported for three term arguments";
    throw IncorrectUsageException(msg);
  }

  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }

  if (yices_term_is_function(yterm0->term) && op.prim_op == Apply)
  {
    return std::make_shared<Yices2Term>(res, true);
  }
  else
  {
    return std::make_shared<Yices2Term>(res);
  }
}

Term Yices2Solver::make_term(Op op, const TermVec & terms) const
{
  size_t size = terms.size();
  term_t res;
  if (!size)
  {
    string msg("Can't apply ");
    msg += op.to_string();
    msg += " to zero terms.";
    throw IncorrectUsageException(msg);
  }
  else if (size == 1)
  {
    return make_term(op, terms[0]);
  }
  else if (size == 2)
  {
    return make_term(op, terms[0], terms[1]);
  }
  else if (size == 3
           && yices_ternary_ops.find(op.prim_op) != yices_ternary_ops.end())
  {
    return make_term(op, terms[0], terms[1], terms[2]);
  }
  else if (op.prim_op == Apply)
  {
    vector<term_t> yargs;
    yargs.reserve(size);
    shared_ptr<Yices2Term> yterm;

    // skip the first term (that's actually a function)
    for (size_t i = 1; i < terms.size(); i++)
    {
      yterm = static_pointer_cast<Yices2Term>(terms[i]);
      yargs.push_back(yterm->term);
    }

    yterm = static_pointer_cast<Yices2Term>(terms[0]);
    if (!yices_term_is_function(yterm->term))
    {
      string msg(
          "Expecting an uninterpreted function to be used with Apply but got ");
      msg += terms[0]->to_string();
      throw IncorrectUsageException(msg);
    }

    res = yices_application(yterm->term, size - 1, &yargs[0]);
  }
  else if (is_variadic(op.prim_op) || op == Distinct)
  {
    vector<term_t> yargs;
    yargs.reserve(size);
    shared_ptr<Yices2Term> yterm;

    // skip the first term (that's actually a function)
    for (const auto & tt : terms)
    {
      yterm = static_pointer_cast<Yices2Term>(tt);
      yargs.push_back(yterm->term);
    }

    if (yices_variadic_ops.find(op.prim_op) != yices_variadic_ops.end())
    {
      res = yices_variadic_ops.at(op.prim_op)(yargs.size(), yargs.data());
    }
    else
    {
      // assume it's a binary function extended to n args
      auto yices_fun = yices_binary_ops.at(op.prim_op);
      res = yices_fun(yargs[0], yargs[1]);
      for (size_t i = 2; i < size; ++i)
      {
        res = yices_fun(res, yargs[i]);
      }
    }
  }
  else
  {
    string msg("Can't apply ");
    msg += op.to_string();
    msg += " to ";
    msg += ::std::to_string(size);
    msg += " terms.";
    throw IncorrectUsageException(msg);
  }

  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }

  return std::make_shared<Yices2Term>(res);
}

void Yices2Solver::reset()
{
  // yices_reset deletes every context and configuration, so free ours
  // first rather than leave the destructor to free them again
  if (ctx)
  {
    yices_free_context(ctx);
    ctx = nullptr;
  }
  yices_free_config(config);
  yices_reset();
  config = yices_new_config();
  symbol_table.clear();
}

void Yices2Solver::reset_assertions()
{
  if (ctx)
  {
    yices_reset_context(ctx);
  }
}

Term Yices2Solver::substitute(const Term term,
                              const UnorderedTermMap & substitution_map) const
{
  shared_ptr<Yices2Term> yterm = static_pointer_cast<Yices2Term>(term);

  vector<term_t> to_subst;
  vector<term_t> values;

  shared_ptr<Yices2Term> tmp_key;
  shared_ptr<Yices2Term> tmp_val;

  for (auto elem : substitution_map)
  {
    tmp_key = static_pointer_cast<Yices2Term>(elem.first);

    to_subst.push_back(tmp_key->term);
    tmp_val = static_pointer_cast<Yices2Term>(elem.second);

    values.push_back(tmp_val->term);
  }

  term_t res =
      yices_subst_term(to_subst.size(), &to_subst[0], &values[0], yterm->term);

  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }

  return std::make_shared<Yices2Term>(res);
}

// helpers
void Yices2Solver::timelimit_start()
{
  if (time_limit)
  {
    signal(SIGALRM, yices2_timelimit_handler);
    assert(running_ctx == nullptr);
    assert(!yices2_terminated);
    running_ctx = get_context();
    itimerval timer{};
    timer.it_value.tv_sec = static_cast<time_t>(time_limit);
    timer.it_value.tv_usec =
        static_cast<suseconds_t>((time_limit - timer.it_value.tv_sec) * 1e6);
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
