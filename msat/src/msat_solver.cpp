/*********************                                                        */
/*! \file msat_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief MathSAT implementation of AbsSmtSolver
**
**
**/

#include "msat_solver.h"
#include "msat_extensions.h"
#include "msat_sort.h"
#include "msat_term.h"

#include <sstream>
#include <unordered_map>
#include <vector>

#include "exceptions.h"
#include "result.h"
#include "solver_utils.h"

using namespace std;

namespace smt {

const unordered_map<string, string> msat_option_map({
         {"produce-models", "model_generation"}
  });

/* MathSAT op mappings */
typedef msat_term (*msat_un_fun)(msat_env, msat_term);
typedef msat_term (*msat_bin_fun)(msat_env, msat_term, msat_term);
typedef msat_term (*msat_tern_fun)(msat_env, msat_term, msat_term, msat_term);

// TODO: implement the external functions
const unordered_map<PrimOp, msat_un_fun> msat_unary_ops({
    { Not, msat_make_not },
    { Negate, ext_msat_make_negate },
    { Abs, ext_msat_make_abs },
    { To_Real, ext_msat_make_nop },
    { To_Int, msat_make_floor },
    { Is_Int, ext_msat_is_int },
    // Indexed Op
    // {Extract, },
    { BVNot, msat_make_bv_not },
    { BVNeg, msat_make_bv_neg },
    // Indexed Ops
    // { Zero_Extend, }
    // { Sign_Extend, }
    // { Repeat, }
    // { Rotate_Left, }
    // { Rotate_Right, }
    // BitVector conversion
    { BV_To_Nat, msat_make_int_from_ubv },
    { UBV_To_Int, msat_make_int_from_ubv },
    { SBV_To_Int, msat_make_int_from_sbv },
    // Indexed Op
    // { Int_To_BV, }
    // Special case
});

const unordered_map<PrimOp, msat_bin_fun> msat_binary_ops(
    { { And, msat_make_and },
      { Or, msat_make_or },
      { Xor, ext_msat_make_xor },
      { Implies, ext_msat_make_implies },
      { Equal, msat_make_eq },
      { Distinct, ext_msat_make_distinct },
      { Plus, msat_make_plus },
      { Minus, ext_msat_make_minus },
      { Mult, msat_make_times },
      { Div, msat_make_divide },
      { IntDiv, ext_msat_make_intdiv },
      { Lt, ext_msat_make_lt },
      { Le, msat_make_leq },
      { Gt, ext_msat_make_gt },
      { Ge, ext_msat_make_geq },
      { Mod, ext_msat_make_mod },
      { Pow, msat_make_pow },
      { Concat, msat_make_bv_concat },
      { BVAnd, msat_make_bv_and },
      { BVOr, msat_make_bv_or },
      { BVXor, msat_make_bv_xor },
      { BVNand, ext_msat_make_bv_nand },
      { BVNor, ext_msat_make_bv_nor },
      { BVXnor, ext_msat_make_bv_xnor },
      { BVComp, msat_make_bv_comp },
      { BVAdd, msat_make_bv_plus },
      { BVSub, msat_make_bv_minus },
      { BVMul, msat_make_bv_times },
      { BVUdiv, msat_make_bv_udiv },
      { BVSdiv, msat_make_bv_sdiv },
      { BVUrem, msat_make_bv_urem },
      { BVSrem, msat_make_bv_srem },
      // TODO: figure out how to implement this
      //       tbh I don't really understand what smod does
      { BVSmod, ext_msat_make_bv_smod },
      { BVShl, msat_make_bv_lshl },
      { BVAshr, msat_make_bv_ashr },
      { BVLshr, msat_make_bv_lshr },
      { BVUlt, msat_make_bv_ult },
      { BVUle, msat_make_bv_uleq },
      { BVUgt, ext_msat_make_bv_ugt },
      { BVUge, ext_msat_make_bv_ugeq },
      { BVSlt, msat_make_bv_slt },
      { BVSle, msat_make_bv_sleq },
      { BVSgt, ext_msat_make_bv_sgt },
      { BVSge, ext_msat_make_bv_sgeq },
      { Select, msat_make_array_read },
      { Forall, msat_make_forall },
      { Exists, msat_make_exists } });

const unordered_map<PrimOp, msat_tern_fun> msat_ternary_ops(
    { { Ite, ext_msat_make_ite }, { Store, msat_make_array_write } });

// other special cases:
// Apply -- needs to handle arbitrarily many terms

// MsatSolver implementation

void MsatSolver::set_opt(const string option, const string value)
{
  // Note: mathsat needs options to be set on a configuration before creating an
  // environment. To handle this we lazily create the environment when needed
  // Correct usage will call set_logic / set_opt before any other calls

  // TODO although the current interface more like smt-lib, we should consider
  // passing the logic and options to the solver up front (on creation)
  // might make more sense for the API

  if (option == "incremental" || option == "produce-unsat-assumptions")
  {
    if (value == "false")
    {
      cout << "Warning: Option "
           << option
           << " is always enabled in MathSAT backend -- cannot be disabled" << endl;
    }
    return;
  }

  if (!env_uninitialized)
  {
    throw IncorrectUsageException("Must set options before using solver.");
  }

  string msat_option = option;
  auto it = msat_option_map.find(option);
  if (it != msat_option_map.end())
  {
    msat_option = it->second;
  }

  // returns zero on success
  if (msat_set_option(cfg, msat_option.c_str(), value.c_str()))
  {
    throw InternalSolverException("Option " + msat_option + " unsupported in mathsat.");
  }
}

void MsatSolver::set_logic(const std::string log)
{
  // TODO: See if there's a correct way to do this
  // this seems like a no-op (doesn't complain for other sorts)
  msat_set_option(cfg, "logic", log.c_str());
  logic = log;
}

void MsatSolver::assert_formula(const Term & t)
{
  initialize_env();
  shared_ptr<MsatTerm> mterm = static_pointer_cast<MsatTerm>(t);
  if (msat_assert_formula(env, mterm->term))
  {
    string msg("Cannot assert term: ");
    msg += t->to_string();
    throw IncorrectUsageException(msg);
  }

  if (!msat_num_backtrack_points(env))
  {
    // keep track of base-level assertions
    base_assertions_.push_back(mterm->term);
  }
}

Result MsatSolver::check_sat()
{
  initialize_env();
  last_query_assuming = false;
  clear_assumption_clauses();
  msat_result mres = msat_solve(env);

  if (mres == MSAT_SAT)
  {
    return Result(SAT);
  }
  else if (mres == MSAT_UNSAT)
  {
    return Result(UNSAT);
  }
  else
  {
    return Result(UNKNOWN);
  }
}

Result MsatSolver::check_sat_assuming(const TermVec & assumptions)
{
  initialize_env();
  last_query_assuming = true;
  clear_assumption_clauses();
  size_t num_assumps = assumptions.size();
  vector<msat_term> m_assumps;
  m_assumps.reserve(num_assumps);

  msat_term ma;
  for (size_t i = 0; i < num_assumps; ++i)
  {
    ma = static_pointer_cast<MsatTerm>(assumptions[i])->term;
    m_assumps.push_back(ma);
  }

  return check_sat_assuming_msatvec(m_assumps);
}

Result MsatSolver::check_sat_assuming_list(const TermList & assumptions)
{
  initialize_env();
  clear_assumption_clauses();
  // expecting (possibly negated) boolean literals
  for (const auto & a : assumptions)
  {
    if (!a->is_symbolic_const() || a->get_sort()->get_sort_kind() != BOOL)
    {
      if (a->get_op() == Not && (*a->begin())->is_symbolic_const())
      {
        continue;
      }
      else
      {
        throw IncorrectUsageException(
            "Expecting boolean indicator literals but got: " + a->to_string());
      }
    }
  }

  vector<msat_term> m_assumps;
  m_assumps.reserve(assumptions.size());

  shared_ptr<MsatTerm> ma;
  for (const auto & a : assumptions)
  {
    ma = static_pointer_cast<MsatTerm>(a);
    m_assumps.push_back(ma->term);
  }

  return check_sat_assuming_msatvec(m_assumps);
}

Result MsatSolver::check_sat_assuming_set(const UnorderedTermSet & assumptions)
{
  initialize_env();
  clear_assumption_clauses();
  // expecting (possibly negated) boolean literals
  for (const auto & a : assumptions)
  {
    if (!a->is_symbolic_const() || a->get_sort()->get_sort_kind() != BOOL)
    {
      if (a->get_op() == Not && (*a->begin())->is_symbolic_const())
      {
        continue;
      }
      else
      {
        throw IncorrectUsageException(
            "Expecting boolean indicator literals but got: " + a->to_string());
      }
    }
  }

  vector<msat_term> m_assumps;
  m_assumps.reserve(assumptions.size());

  shared_ptr<MsatTerm> ma;
  for (const auto & a : assumptions)
  {
    ma = static_pointer_cast<MsatTerm>(a);
    m_assumps.push_back(ma->term);
  }

  return check_sat_assuming_msatvec(m_assumps);
}

void MsatSolver::push(uint64_t num)
{
  initialize_env();
  for (uint64_t i = 0; i < num; i++)
  {
    msat_push_backtrack_point(env);
  }
}

void MsatSolver::pop(uint64_t num)
{
  initialize_env();
  for (uint64_t i = 0; i < num; i++)
  {
    msat_pop_backtrack_point(env);
  }
}

uint64_t MsatSolver::get_context_level() const
{
  return msat_num_backtrack_points(env);
}

Term MsatSolver::get_value(const Term & t) const
{
  initialize_env();
  shared_ptr<MsatTerm> mterm = static_pointer_cast<MsatTerm>(t);
  msat_term val = msat_get_model_value(env, mterm->term);

  if (MSAT_ERROR_TERM(val))
  {
    string msg("Error getting value for ");
    msg += t->to_string();
    msg +=
        ".\nBe sure the last check-sat call was sat and the term only contains "
        "constants in this solving environment.";
    throw IncorrectUsageException(msg);
  }

  return std::make_shared<MsatTerm> (env, val);
}

UnorderedTermMap MsatSolver::get_array_values(const Term & arr,
                                              Term & out_const_base) const
{
  initialize_env();
  UnorderedTermMap assignments;
  out_const_base = nullptr;

  shared_ptr<MsatTerm> marr = static_pointer_cast<MsatTerm>(arr);
  msat_term mval = msat_get_model_value(env, marr->term);

  Term idx;
  Term val;
  while (msat_term_is_array_write(env, mval))
  {
    idx = std::make_shared<MsatTerm>(env, msat_term_get_arg(mval, 1));
    val = std::make_shared<MsatTerm>(env, msat_term_get_arg(mval, 2));
    assignments[idx] = val;
    mval = msat_term_get_arg(mval, 0);
  }

  if (msat_term_is_array_const(env, mval))
  {
    out_const_base =
        std::make_shared<MsatTerm>(env, msat_term_get_arg(mval, 0));
  }

  return assignments;
}

void MsatSolver::get_unsat_assumptions(UnorderedTermSet & out)
{
  initialize_env();
  size_t core_size;
  msat_term * mcore = msat_get_unsat_assumptions(env, &core_size);
  if (!last_query_assuming)
  {
    throw SmtException(
        "Called get_unsat_assumptions after check-sat, or "
        "check-sat-assuming with no assumptions. Should be "
        "used after a non-trivial call to check-sat-assuming.");
  }
  msat_term * mcore_iter = mcore;
  for (size_t i = 0; i < core_size; ++i)
  {
    if (MSAT_ERROR_TERM(*mcore_iter))
    {
      throw InternalSolverException("got an error term in the unsat core");
    }
    out.insert(std::make_shared<MsatTerm>(env, assumption_map_.at(msat_term_id(*mcore_iter))));
    ++mcore_iter;
  }
  msat_free(mcore);
}

Sort MsatSolver::make_sort(const std::string name, uint64_t arity) const
{
  initialize_env();
  if (!arity)
  {
    return std::make_shared<MsatSort> (env,
                                       msat_get_simple_type(env, name.c_str()));
  }
  else
  {
    throw NotImplementedException(
        "Uninterpreted sorts with non-zero arity not supported through MathSAT "
        "api.");
  }
}

Sort MsatSolver::make_sort(SortKind sk) const
{
  initialize_env();
  if (sk == BOOL)
  {
    return std::make_shared<MsatSort> (env, msat_get_bool_type(env));
  }
  else if (sk == INT)
  {
    return std::make_shared<MsatSort> (env, msat_get_integer_type(env));
  }
  else if (sk == REAL)
  {
    return std::make_shared<MsatSort> (env, msat_get_rational_type(env));
  }
  else
  {
    std::string msg("Can't create sort with sort constructor ");
    msg += to_string(sk);
    msg += " and no arguments";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort MsatSolver::make_sort(SortKind sk, uint64_t size) const
{
  initialize_env();
  if (sk == BV)
  {
    return std::make_shared<MsatSort> (env, msat_get_bv_type(env, size));
  }
  else
  {
    std::string msg("Can't create sort with sort constructor ");
    msg += to_string(sk);
    msg += " and an integer argument";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort MsatSolver::make_sort(SortKind sk, const Sort & sort1) const
{
  initialize_env();
  throw NotImplementedException(
      "Smt-switch does not have any sorts that take one sort parameter yet.");
}

Sort MsatSolver::make_sort(SortKind sk,
                           const Sort & sort1,
                           const Sort & sort2) const
{
  initialize_env();
  if (sk == ARRAY)
  {
    std::shared_ptr<MsatSort> midxsort =
        std::static_pointer_cast<MsatSort>(sort1);
    std::shared_ptr<MsatSort> melemsort =
        std::static_pointer_cast<MsatSort>(sort2);
    return std::make_shared<MsatSort>
        (env, msat_get_array_type(env, midxsort->type, melemsort->type));
  }
  else
  {
    std::string msg("Can't create sort with sort constructor ");
    msg += to_string(sk);
    msg += " and two Sort arguments";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort MsatSolver::make_sort(SortKind sk,
                           const Sort & sort1,
                           const Sort & sort2,
                           const Sort & sort3) const
{
  throw NotImplementedException(
      "Smt-switch does not have any sorts that take three sort parameters "
      "yet.");
}

Sort MsatSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  initialize_env();
  if (sk == FUNCTION)
  {
    if (sorts.size() < 2)
    {
      throw IncorrectUsageException(
          "Function sort must have >=2 sort arguments.");
    }

    // arity is one less, because last sort is return sort
    uint32_t arity = sorts.size() - 1;

    string decl_name("internal_ref_fun");

    std::vector<msat_type> msorts;
    msorts.reserve(arity);
    msat_type msort;
    for (uint32_t i = 0; i < arity; i++)
    {
      msort = std::static_pointer_cast<MsatSort>(sorts[i])->type;
      if (msat_is_bool_type(env, msort))
      {
        // mathsat does not support functions of booleans
        // convert to width one bitvector instead
        msort = msat_get_bv_type(env, 1);
      }
      msorts.push_back(msort);
      decl_name += ("_" + sorts[i]->to_string());
    }
    Sort sort = sorts.back();
    msort = std::static_pointer_cast<MsatSort>(sort)->type;
    decl_name += ("_return_" + sort->to_string());
    msat_type mfunsort = msat_get_function_type(env, &msorts[0], arity, msort);

    // creating a reference decl, because it's the only way to get codomain and
    // domain sorts i.e. there's no msat_is_function_type(msat_env, msat_type)
    msat_decl ref_fun_decl =
        msat_declare_function(env, decl_name.c_str(), mfunsort);

    return std::make_shared<MsatSort> (env, mfunsort, ref_fun_decl);
  }
  else if (sorts.size() == 1)
  {
    return make_sort(sk, sorts[0]);
  }
  else if (sorts.size() == 2)
  {
    return make_sort(sk, sorts[0], sorts[1]);
  }
  else if (sorts.size() == 3)
  {
    return make_sort(sk, sorts[0], sorts[1], sorts[2]);
  }
  else
  {
    std::string msg("Can't create sort from sort constructor ");
    msg += to_string(sk);
    msg += " with a vector of sorts";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort MsatSolver::make_sort(const Sort & sort_con, const SortVec & sorts) const
{
  throw NotImplementedException(
      "MathSAT does not support uninterpreted sort constructors");
}

Sort MsatSolver::make_sort(const DatatypeDecl & d) const {
  throw NotImplementedException("MsatSolver::make_sort");
};

DatatypeDecl MsatSolver::make_datatype_decl(const std::string & s)  {
    throw NotImplementedException("MsatSolver::make_datatype_decl");
}

DatatypeConstructorDecl MsatSolver::make_datatype_constructor_decl(
    const std::string s)
{
  throw NotImplementedException("MsatSolver::make_datatype_constructor_decl");
}

void MsatSolver::add_constructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const {
  throw NotImplementedException("MsatSolver::add_constructor");
}

void MsatSolver::add_selector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const {
  throw NotImplementedException("MsatSolver::add_selector");
}

void MsatSolver::add_selector_self(DatatypeConstructorDecl & dt, const std::string & name) const {
  throw NotImplementedException("MsatSolver::add_selector_self");
}

Term MsatSolver::get_constructor(const Sort & s, std::string name) const  {
  throw NotImplementedException("MsatSolver::get_constructor");
}

Term MsatSolver::get_tester(const Sort & s, std::string name) const  {
  throw NotImplementedException("MsatSolver::get_testeer");
}

Term MsatSolver::get_selector(const Sort & s, std::string con, std::string name) const  {
  throw NotImplementedException("MsatSolver::get_selector");
}

Term MsatSolver::make_term(bool b) const
{
  initialize_env();
  if (b)
  {
    return std::make_shared<MsatTerm> (env, msat_make_true(env));
  }
  else
  {
    return std::make_shared<MsatTerm> (env, msat_make_false(env));
  }
}

Term MsatSolver::make_term(int64_t i, const Sort & sort) const
{
  initialize_env();
  try
  {
    SortKind sk = sort->get_sort_kind();
    if (sk == BV)
    {
      // always use string version for consistency
      std::string sval = std::to_string(i);
      msat_term mval = ext_msat_make_bv_number(env, sval.c_str(), sort->get_width(), 10);
      if (MSAT_ERROR_TERM(mval))
      {
        throw IncorrectUsageException("");
      }
      return std::make_shared<MsatTerm> (env, mval);
    }
    else if (sk == REAL || sk == INT)
    {
      msat_term mval = msat_make_int_number(env, i);
      if (MSAT_ERROR_TERM(mval))
      {
        throw IncorrectUsageException("");
      }
      return std::make_shared<MsatTerm> (env, mval);
    }
    else
    {
      throw IncorrectUsageException("");
    }
  }
  catch(IncorrectUsageException & e)
  {
    string msg("Can't create value ");
    msg += i;
    msg += " with sort ";
    msg += sort->to_string();
    throw IncorrectUsageException(msg);
  }
}

Term MsatSolver::make_term(const std::string val,
                           const Sort & sort,
                           uint64_t base) const
{
  initialize_env();
  try
  {
    SortKind sk = sort->get_sort_kind();
    if (sk == BV)
    {
      msat_term mval = ext_msat_make_bv_number(env, val.c_str(), sort->get_width(), base);
      if (MSAT_ERROR_TERM(mval))
      {
        throw IncorrectUsageException("");
      }
      return std::make_shared<MsatTerm> (env, mval);
    }
    else if (sk == REAL || sk == INT)
    {
      if (base != 10)
      {
        throw NotImplementedException(
                                      "MathSAT only supports base 10 for real and integer values");
      }

      msat_term mval = msat_make_number(env, val.c_str());
      if (MSAT_ERROR_TERM(mval))
      {
        throw IncorrectUsageException("");
      }
      return std::make_shared<MsatTerm> (env, mval);
    }
    else
    {
      throw IncorrectUsageException("");
    }
  }
  catch(IncorrectUsageException & e)
  {
    string msg("Can't create value ");
    msg += val;
    msg += " with sort ";
    msg += sort->to_string();
    throw IncorrectUsageException(msg);
  }
}

Term MsatSolver::make_term(const Term & val, const Sort & sort) const
{
  initialize_env();
  if (sort->get_sort_kind() != ARRAY)
  {
    throw IncorrectUsageException(
        "Expecting to create a const array but got a non array sort");
  }
  shared_ptr<MsatSort> msort = static_pointer_cast<MsatSort>(sort);
  shared_ptr<MsatTerm> mval = static_pointer_cast<MsatTerm>(val);
  return std::make_shared<MsatTerm>
      (env, msat_make_array_const(env, msort->type, mval->term));
}

Term MsatSolver::make_symbol(const string name, const Sort & sort)
{
  initialize_env();
  msat_decl decl = msat_find_decl(env, name.c_str());
  if (!MSAT_ERROR_DECL(decl))
  {
    // symbol already exists
    string msg("Symbol name ");
    msg += name;
    msg += " has already used.";
    throw IncorrectUsageException(msg);
  }

  shared_ptr<MsatSort> msort = static_pointer_cast<MsatSort>(sort);
  if (MSAT_ERROR_TYPE(msort->type))
  {
    throw InternalSolverException("Got error type in MathSAT backend.");
  }

  decl = msat_declare_function(env, name.c_str(), msort->type);

  if (MSAT_ERROR_DECL(decl) && name.empty())
  {
    decl = msat_declare_function(env, "||", msort->type);
  }
  else if (MSAT_ERROR_DECL(decl))
  {
    throw SmtException("Got msat error decl when creating " +
                       name + " of sort " + sort->to_string());
  }

  if (sort->get_sort_kind() == FUNCTION)
  {
    return std::make_shared<MsatTerm> (env, decl);
  }
  else
  {
    msat_term res = msat_make_constant(env, decl);
    if (MSAT_ERROR_TERM(res))
    {
      throw InternalSolverException("Got error term.");
    }
    return std::make_shared<MsatTerm> (env, res);
  }
}

Term MsatSolver::get_symbol(const std::string & name)
{
  msat_decl decl = msat_find_decl(env, name.c_str());
  if (MSAT_ERROR_DECL(decl))
  {
    // symbol already exists
    string msg("Symbol named ");
    msg += name;
    msg += " does not exist.";
    throw IncorrectUsageException(msg);
  }

  msat_term res = msat_make_constant(env, decl);
  if (MSAT_ERROR_TERM(res))
  {
    // assume it is a function
    return std::make_shared<MsatTerm>(env, decl);
  }
  return std::make_shared<MsatTerm>(env, res);
}

Term MsatSolver::make_param(const std::string name, const Sort & sort)
{
  initialize_env();
  shared_ptr<MsatSort> msort = static_pointer_cast<MsatSort>(sort);
  msat_term var = msat_make_variable(env, name.c_str(), msort->type);
  return std::make_shared<MsatTerm>(env, var);
}

Term MsatSolver::make_term(Op op, const Term & t) const
{
  initialize_env();
  shared_ptr<MsatTerm> mterm = static_pointer_cast<MsatTerm>(t);
  msat_term res;
  if (!op.num_idx)
  {
    if (msat_unary_ops.find(op.prim_op) != msat_unary_ops.end())
    {
      res = msat_unary_ops.at(op.prim_op)(env, mterm->term);
    }
    else
    {
      string msg("Can't apply ");
      msg += op.to_string();
      msg += " to a single term, or not supported by MathSAT backend yet.";
      throw IncorrectUsageException(msg);
    }
  }
  else if (op.prim_op == Extract)
  {
    if (op.idx0 < 0 || op.idx1 < 0)
    {
      throw IncorrectUsageException("Can't have negative number in extract");
    }
    res = msat_make_bv_extract(env, op.idx0, op.idx1, mterm->term);
  }
  else if (op.prim_op == Zero_Extend)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException("Can't zero extend by negative number");
    }
    res = msat_make_bv_zext(env, op.idx0, mterm->term);
  }
  else if (op.prim_op == Sign_Extend)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException("Can't sign extend by negative number");
    }
    res = msat_make_bv_sext(env, op.idx0, mterm->term);
  }
  else if (op.prim_op == Repeat)
  {
    if (op.num_idx < 1)
    {
      throw IncorrectUsageException("Can't create repeat with index < 1");
    }
    res = mterm->term;
    for (size_t i = 1; i < op.idx0; i++)
    {
      res = msat_make_bv_concat(env, mterm->term, res);
    }
  }
  else if (op.prim_op == Rotate_Left)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException("Can't rotate by negative number");
    }
    res = msat_make_bv_rol(env, op.idx0, mterm->term);
  }
  else if (op.prim_op == Rotate_Right)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException("Can't rotate by negative number");
    }
    res = msat_make_bv_ror(env, op.idx0, mterm->term);
  }
  else if (op.prim_op == Int_To_BV)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException(
          "Can't have negative width in Int_To_BV op");
    }
    res = msat_make_int_to_bv(env, op.idx0, mterm->term);
  }
  else
  {
    string msg("Can't apply ");
    msg += op.to_string();
    msg += " to ";
    msg += t->to_string();
    throw IncorrectUsageException(msg);
  }

  if (MSAT_ERROR_TERM(res))
  {
    string msg("Failed to create term given ");
    msg += op.to_string();
    msg += " and ";
    msg += t->to_string();
    throw InternalSolverException(msg);
  }
  else
  {
    return std::make_shared<MsatTerm> (env, res);
  }
}

Term MsatSolver::make_term(Op op, const Term & t0, const Term & t1) const
{
  initialize_env();
  shared_ptr<MsatTerm> mterm0 = static_pointer_cast<MsatTerm>(t0);
  shared_ptr<MsatTerm> mterm1 = static_pointer_cast<MsatTerm>(t1);
  msat_term res;
  if (!op.num_idx)
  {
    if (msat_binary_ops.find(op.prim_op) != msat_binary_ops.end())
    {
      res = msat_binary_ops.at(op.prim_op)(env, mterm0->term, mterm1->term);
    }
    else if (op.prim_op == Apply)
    {
      if (!mterm0->is_uf)
      {
        throw IncorrectUsageException("Expecting UF as first argument to Apply");
      }
      vector<msat_term> v({mterm1->term});
      res = ext_msat_make_uf(env, mterm0->decl, v);
    }
    else
    {
      string msg("Can't apply ");
      msg += op.to_string();
      msg += " to two terms, or not supported by MathSAT backend yet.";
      throw IncorrectUsageException(msg);
    }
  }
  else
  {
    string msg = op.to_string();
    msg += " not supported for two term arguments";
    throw IncorrectUsageException(msg);
  }

  if (MSAT_ERROR_TERM(res))
  {
    string msg("Failed to create term given ");
    msg += op.to_string();
    msg += " and ";
    msg += t0->to_string() + ", " + t1->to_string();
    throw InternalSolverException(msg);
  }
  else
  {
    return std::make_shared<MsatTerm> (env, res);
  }
}

Term MsatSolver::make_term(Op op,
                           const Term & t0,
                           const Term & t1,
                           const Term & t2) const
{
  initialize_env();
  shared_ptr<MsatTerm> mterm0 = static_pointer_cast<MsatTerm>(t0);
  shared_ptr<MsatTerm> mterm1 = static_pointer_cast<MsatTerm>(t1);
  shared_ptr<MsatTerm> mterm2 = static_pointer_cast<MsatTerm>(t2);
  msat_term res;
  if (!op.num_idx)
  {
    if (msat_ternary_ops.find(op.prim_op) != msat_ternary_ops.end())
    {
      res = msat_ternary_ops.at(op.prim_op)(
                                            env, mterm0->term, mterm1->term, mterm2->term);
    }
    else if (op.prim_op == Apply)
    {
      if (!mterm0->is_uf)
      {
        throw IncorrectUsageException("Expecting UF as first argument to Apply");
      }
      vector<msat_term> v({mterm1->term, mterm2->term});
      res = ext_msat_make_uf(env, mterm0->decl, v);
    }
    else if (op.prim_op == Forall)
    {
      res = msat_make_forall(env, mterm1->term, mterm2->term);
      res = msat_make_forall(env, mterm0->term, res);
    }
    else if (op.prim_op == Exists)
    {
      res = msat_make_exists(env, mterm1->term, mterm2->term);
      res = msat_make_exists(env, mterm0->term, res);
    }
    else
    {
      string msg("Can't apply ");
      msg += op.to_string();
      msg += " to three terms, or not supported by MathSAT backend yet.";
      throw IncorrectUsageException(msg);
    }
  }
  else
  {
    string msg = op.to_string();
    msg += " not supported for three term arguments";
    throw IncorrectUsageException(msg);
  }

  if (MSAT_ERROR_TERM(res))
  {
    string msg("Failed to create term given ");
    msg += op.to_string();
    msg += " and ";
    msg += t0->to_string() + ", " + t1->to_string() + ", " + t2->to_string();
    throw InternalSolverException(msg);
  }
  else
  {
    return std::make_shared<MsatTerm> (env, res);
  }
}

Term MsatSolver::make_term(Op op, const TermVec & terms) const
{
  initialize_env();
  size_t size = terms.size();
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
           && msat_ternary_ops.find(op.prim_op) != msat_ternary_ops.end())
  {
    return make_term(op, terms[0], terms[1], terms[2]);
  }
  else if (op.prim_op == Apply)
  {
    vector<msat_term> margs;
    margs.reserve(size);
    shared_ptr<MsatTerm> mterm;

    // skip the first term (that's actually a function)
    for (size_t i = 1; i < terms.size(); i++)
    {
      mterm = static_pointer_cast<MsatTerm>(terms[i]);
      margs.push_back(mterm->term);
    }

    mterm = static_pointer_cast<MsatTerm>(terms[0]);
    if (!mterm->is_uf)
    {
      string msg(
          "Expecting an uninterpreted function to be used with Apply but got ");
      msg += terms[0]->to_string();
      throw IncorrectUsageException(msg);
    }
    msat_decl uf = mterm->decl;
    msat_term res = ext_msat_make_uf(env, uf, margs);
    if (MSAT_ERROR_TERM(res))
    {
      string msg("Failed to create term given ");
      msg += op.to_string();
      msg += " and ";
      for (auto t : terms)
      {
        msg += " " + t->to_string() + ",";
      }
      throw InternalSolverException(msg);
    }
    return make_shared<MsatTerm>(env, res);
  }
  else if (is_variadic(op.prim_op))
  {
    // assuming it is a binary operator extended to n arguments
    auto msat_fun = msat_binary_ops.at(op.prim_op);

    vector<msat_term> margs;
    margs.reserve(terms.size());
    for (const auto & tt : terms)
    {
      margs.push_back(static_pointer_cast<MsatTerm>(tt)->term);
    }
    msat_term res = msat_fun(env, margs[0], margs[1]);
    for (size_t i = 2; i < margs.size(); ++i)
    {
      res = msat_fun(env, res, margs[i]);
    }
    return make_shared<MsatTerm>(env, res);
  }
  else if (op == Forall || op == Exists)
  {
    vector<msat_term> mterms;
    mterms.reserve(terms.size());
    for (const auto & tt : terms)
    {
      mterms.push_back(static_pointer_cast<MsatTerm>(tt)->term);
    }

    msat_term res = mterms.back();
    mterms.pop_back();
    while (mterms.size())
    {
      msat_term t = mterms.back();
      mterms.pop_back();
      if (op == Forall)
      {
        res = msat_make_forall(env, t, res);
      }
      else
      {
        res = msat_make_exists(env, t, res);
      }
    }
    return make_shared<MsatTerm>(env, res);
  }
  else if (op.prim_op == Distinct)
  {
    // special case for distinct
    // need to apply to O(n^2) distinct pairs
    return make_distinct(this, terms);
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
}

void MsatSolver::reset()
{
  if (!env_uninitialized)
  {
    msat_destroy_env(env);
  }
  msat_destroy_config(cfg);

  cfg = msat_create_config();
  env = msat_create_env(cfg);
}

void MsatSolver::reset_assertions()
{
  initialize_env();
  msat_reset_env(env);
  base_assertions_.clear();
}

Term MsatSolver::substitute(const Term term,
                            const UnorderedTermMap & substitution_map) const
{
  initialize_env();
  shared_ptr<MsatTerm> mterm = static_pointer_cast<MsatTerm>(term);

  vector<msat_term> to_subst;
  vector<msat_term> values;

  shared_ptr<MsatTerm> tmp_key;
  shared_ptr<MsatTerm> tmp_val;
  // TODO: Fallback to parent class implementation if there are uninterpreted
  // functions
  //       in the map
  for (auto elem : substitution_map)
  {
    tmp_key = static_pointer_cast<MsatTerm>(elem.first);
    if (tmp_key->is_uf)
    {
      throw NotImplementedException(
          "MathSAT does not support substituting functions");
    }
    to_subst.push_back(tmp_key->term);
    tmp_val = static_pointer_cast<MsatTerm>(elem.second);
    if (tmp_val->is_uf)
    {
      throw NotImplementedException(
          "MathSAT does not support substituting functions");
    }
    values.push_back(tmp_val->term);
  }

  // TODO: add guarded assertion in debug mode about size of vectors

  msat_term res = msat_apply_substitution(
      env, mterm->term, to_subst.size(), &to_subst[0], &values[0]);

  return Term(new MsatTerm(env, res));
}

void MsatSolver::dump_smt2(std::string filename) const
{
  initialize_env();
  size_t num_asserted;
  msat_term * assertions = msat_get_asserted_formulas(env, &num_asserted);
  msat_term all_asserts = msat_make_true(env);
  for (size_t i = 0; i < num_asserted; ++i)
  {
    all_asserts = msat_make_and(env, all_asserts, *assertions);
    ++assertions;
  }
  if (MSAT_ERROR_TERM(all_asserts))
  {
    throw InternalSolverException("Failed to gather all assertions");
  }
  const char * log = logic.empty() ? NULL : logic.c_str();
  FILE * file = fopen(filename.c_str(), "w");
  msat_to_smtlib2_ext_file(env, all_asserts, log, true, file);
  fprintf(file, "\n(check-sat)\n");
  fclose(file);
}

// helpers
msat_term MsatSolver::label(msat_term p) const
{
  initialize_env();

  if (msat_term_is_boolean_constant(env, p) ||
      (msat_term_is_not(env, p) && msat_term_is_boolean_constant(env, msat_term_get_arg(p, 0))))
  {
    // if a (negated) boolean constant, don't need a fresh label
    return p;
  }

  std::ostringstream buf;
  buf << ".assump_lbl{" << msat_term_id(p) << "}";
  std::string name = buf.str();
  msat_decl d =
      msat_declare_function(env, name.c_str(), msat_get_bool_type(env));
  // if it already existed, mathsat gives the same symbol
  // in this case, those semantics are perfect -- we don't need a cache
  return msat_make_constant(env, d);
}

// end MsatSolver implementation

// begin MsatInterpolatingSolver implementation

void MsatInterpolatingSolver::set_opt(const string option, const string value)
{
  throw IncorrectUsageException("Can't set options of interpolating solver.");
}

void MsatInterpolatingSolver::push(uint64_t num)
{
  throw IncorrectUsageException("Can't call push from interpolating solver");
}

void MsatInterpolatingSolver::pop(uint64_t num)
{
  throw IncorrectUsageException("Can't call pop from interpolating solver");
}

void MsatInterpolatingSolver::assert_formula(const Term & t)
{
  throw IncorrectUsageException(
      "Can't assert formulas in interpolating solver");
}

Result MsatInterpolatingSolver::check_sat()
{
  throw IncorrectUsageException(
      "Can't call check_sat from interpolating solver");
}

Result MsatInterpolatingSolver::check_sat_assuming(const TermVec & assumptions)
{
  throw IncorrectUsageException(
      "Can't call check_sat_assuming from interpolating solver");
}

Term MsatInterpolatingSolver::get_value(const Term & t) const
{
  throw IncorrectUsageException("Can't get values from interpolating solver");
}

// delegate the interpolation procedure to `get_sequence_interpolants`
Result MsatInterpolatingSolver::get_interpolant(const Term & A,
                                                const Term & B,
                                                Term & out_I) const
{
  TermVec formulas{ A, B };
  TermVec itp_seq;
  Result res = get_sequence_interpolants(formulas, itp_seq);
  assert(itp_seq.empty() <= 1);
  if (itp_seq.size() == 1)
  {
    out_I = itp_seq.front();
  }
  return res;
}

// Compute interpolation sequence with incremental solving.
// The function trys to reuse as many previously-asserted formulas as possible.
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
// The folllowing invariant should hold before and after the call:
// `#msat-backtrack-points == assertions_.size() == interp_grps_.size()`
Result MsatInterpolatingSolver::get_sequence_interpolants(
    const TermVec & formulae, TermVec & out_I) const
{
  initialize_env();
  assert(msat_num_backtrack_points(env) == assertions_.size());
  assert(interp_grps_.size() == assertions_.size());

  // check which assertions can be reused
  for (size_t i = 0; i < assertions_.size() && i < formulae.size(); ++i)
  {
    if (assertions_.at(i) != formulae.at(i))
    {
      if (i == 0)
      {
        // no reusable formulas, simply reset
        msat_reset_env(env);
      }
      else
      {
        // pop formulas that cannot be reused
        for (size_t j = i; j < assertions_.size(); ++j)
        {
          msat_pop_backtrack_point(env);
        }
      }
      break;
    }
  }

  const size_t num_reused = msat_num_backtrack_points(env);
  interp_grps_.resize(num_reused);
  interp_grps_.reserve(formulae.size());
  assertions_.resize(num_reused);
  assertions_.reserve(formulae.size());
  for (size_t k = num_reused; k < formulae.size(); ++k)
  {
    // Add a new interpolation group and a new backtrack point
    // then push the formula.
    int grp = msat_create_itp_group(env);
    msat_set_itp_group(env, grp);
    msat_push_backtrack_point(env);
    msat_assert_formula(env,
                        static_pointer_cast<MsatTerm>(formulae.at(k))->term);
    interp_grps_.push_back(grp);
    assertions_.push_back(formulae.at(k));
  }
  assert(interp_grps_.size() == formulae.size());
  assert(interp_grps_.size() == assertions_.size());
  assert(interp_grps_.size() == msat_num_backtrack_points(env));

  msat_result msat_res = msat_solve(env);

  if (msat_res == MSAT_SAT)
  {
    return Result(SAT);
  }
  else if (msat_res == MSAT_UNKNOWN)
  {
    return Result(UNKNOWN, "Interpolation failure.");
  }

  assert(msat_res == MSAT_UNSAT);

  Result r = Result(UNSAT);
  for (size_t i = 1; i < interp_grps_.size(); ++i)
  {
    msat_term mI = msat_get_interpolant(env, interp_grps_.data(), i);
    if (MSAT_ERROR_TERM(mI))
    {
      // add a null term -- see solver.h documentation for this function
      Term nullterm;
      out_I.push_back(nullterm);
      r = Result(UNKNOWN,
                 "Had at least one interpolation failure in "
                 "get_sequence_interpolants.");
    }
    else
    {
      out_I.push_back(make_shared<MsatTerm>(env, mI));
    }
  }

  assert(out_I.size() == formulae.size() - 1);
  return r;
}

// end MsatInterpolatingSolver implementation

}  // namespace smt
