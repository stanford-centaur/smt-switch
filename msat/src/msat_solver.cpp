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

using namespace std;

namespace smt {

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
    // Indexed Op
    // { Int_To_BV, }
    // Special case
});

const unordered_map<PrimOp, msat_bin_fun> msat_binary_ops(
    { { And, msat_make_and },
      { Or, msat_make_or },
      { Xor, ext_msat_make_xor },
      { Implies, ext_msat_make_implies },
      { Iff, msat_make_iff },
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
  // environment. To handle this we just set them up front
  //
  // Could also rebuild the environment, but unfortunately it leaks memory
  // technically we should be able to free the environment using
  // msat_destroy_env(env) but it still leaks
  if (option == "produce-models")
  {
    if (value == "false")
    {
      std::cout << "Warning: MathSAT backend always produces models -- it "
                   "can't be disabled."
                << std::endl;
    }
  }
  else if (option == "incremental")
  {
    if (value == "false")
    {
      std::cout << "Warning: MathSAT backend is always incremental -- it can't "
                   "be disabled."
                << std::endl;
    }
  }
  else if (option == "produce-unsat-cores")
  {
    if (value == "false")
    {
      std::cout << "Warning: MathSAT backend is always unsat core producing -- "
                   "it can't "
                   "be disabled."
                << std::endl;
    }
  }
  else
  {
    string msg("Option ");
    msg += option;
    msg += " is not yet supported for the MathSAT backend";
    throw NotImplementedException(msg);
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
  shared_ptr<MsatTerm> mterm = static_pointer_cast<MsatTerm>(t);
  if (msat_assert_formula(env, mterm->term))
  {
    string msg("Cannot assert term: ");
    msg += t->to_string();
    throw IncorrectUsageException(msg);
  }
}

Result MsatSolver::check_sat()
{
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
  // expecting (possibly negated) boolean literals
  for (auto a : assumptions)
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
  for (auto a : assumptions)
  {
    ma = static_pointer_cast<MsatTerm>(a);
    m_assumps.push_back(ma->term);
  }

  msat_result mres =
      msat_solve_with_assumptions(env, &m_assumps[0], m_assumps.size());

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

void MsatSolver::push(uint64_t num)
{
  for (uint64_t i = 0; i < num; i++)
  {
    msat_push_backtrack_point(env);
  }
}

void MsatSolver::pop(uint64_t num)
{
  for (uint64_t i = 0; i < num; i++)
  {
    msat_pop_backtrack_point(env);
  }
}

Term MsatSolver::get_value(const Term & t) const
{
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

TermVec MsatSolver::get_unsat_core()
{
  TermVec core;
  size_t core_size;
  msat_term * mcore = msat_get_unsat_assumptions(env, &core_size);
  if (!mcore || !core_size)
  {
    throw InternalSolverException(
        "Got an empty unsat core. Ensure your last call was unsat and had "
        "assumptions in check_sat_assuming that are required to get an unsat "
        "result");
  }
  msat_term * mcore_iter = mcore;
  for (size_t i = 0; i < core_size; ++i)
  {
    core.push_back(std::make_shared<MsatTerm>(env, *mcore_iter));
    ++mcore_iter;
  }
  msat_free(mcore);
  return core;
}

Sort MsatSolver::make_sort(const std::string name, uint64_t arity) const
{
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
  throw NotImplementedException(
      "Smt-switch does not have any sorts that take one sort parameter yet.");
}

Sort MsatSolver::make_sort(SortKind sk,
                           const Sort & sort1,
                           const Sort & sort2) const
{
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
};
void MsatSolver::add_constructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const {
  throw NotImplementedException("MsatSolver::add_constructor");
};
void MsatSolver::add_selector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const {
  throw NotImplementedException("MsatSolver::add_selector");
};
void MsatSolver::add_selector_self(DatatypeConstructorDecl & dt, const std::string & name) const {
  throw NotImplementedException("MsatSolver::add_selector_self");
};

Term MsatSolver::get_constructor(const Sort & s, std::string name) const  {
  throw NotImplementedException("MsatSolver::get_constructor");
};
Term MsatSolver::get_tester(const Sort & s, std::string name) const  {
  throw NotImplementedException("MsatSolver::get_testeer");
};

Term MsatSolver::get_selector(const Sort & s, std::string con, std::string name) const  {
  throw NotImplementedException("MsatSolver::get_selector");
};


Term MsatSolver::make_term(bool b) const
{
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
  msat_decl decl = msat_find_decl(env, name.c_str());
  if (!MSAT_ERROR_DECL(decl))
  {
    // symbol already exists
    string msg("Symbol ");
    msg += name;
    msg += " already exists.";
    throw IncorrectUsageException(msg);
  }

  shared_ptr<MsatSort> msort = static_pointer_cast<MsatSort>(sort);
  if (MSAT_ERROR_TYPE(msort->type))
  {
    throw InternalSolverException("Got error type in MathSAT backend.");
  }
  decl = msat_declare_function(env, name.c_str(), msort->type);

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

Term MsatSolver::make_param(const std::string name, const Sort & sort)
{
  shared_ptr<MsatSort> msort = static_pointer_cast<MsatSort>(sort);
  msat_term var = msat_make_variable(env, name.c_str(), msort->type);
  return std::make_shared<MsatTerm>(env, var);
}

Term MsatSolver::make_term(Op op, const Term & t) const
{
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
  else if (size == 3)
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
    return Term(new MsatTerm(env, res));
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
  msat_destroy_env(env);
  msat_destroy_config(cfg);

  cfg = msat_create_config();
  env = msat_create_env(cfg);
}

void MsatSolver::reset_assertions() { msat_reset_env(env); }

Term MsatSolver::substitute(const Term term,
                            const UnorderedTermMap & substitution_map) const
{
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
  std::ostringstream buf;
  buf << ".assump_lbl{" << msat_term_id(p) << "}";
  std::string name = buf.str();
  msat_decl d =
      msat_declare_function(env, name.c_str(), msat_get_bool_type(env));
  return msat_make_constant(env, d);
}

// end MsatSolver implementation

// begin MsatInterpolatingSolver implementation

void MsatInterpolatingSolver::set_opt(const string option, const string value)
{
  throw IncorrectUsageException("Can't set options of interpolating solver.");
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

bool MsatInterpolatingSolver::get_interpolant(const Term & A,
                                              const Term & B,
                                              Term & out_I) const
{
  // reset the environment -- each interpolant is it's own separate call
  msat_reset_env(env);

  if (A->get_sort()->get_sort_kind() != BOOL
      || B->get_sort()->get_sort_kind() != BOOL)
  {
    throw IncorrectUsageException("get_interpolant requires two boolean terms");
  }

  msat_term mA = static_pointer_cast<MsatTerm>(A)->term;
  msat_term mB = static_pointer_cast<MsatTerm>(B)->term;

  int group_A = msat_create_itp_group(env);
  int group_B = msat_create_itp_group(env);

  msat_set_itp_group(env, group_A);
  msat_assert_formula(env, mA);
  msat_set_itp_group(env, group_B);
  msat_assert_formula(env, mB);

  msat_result res = msat_solve(env);

  if (res == MSAT_UNSAT)
  {
    msat_term itp = msat_get_interpolant(env, &group_A, 1);
    if (MSAT_ERROR_TERM(itp))
    {
      throw InternalSolverException("Failed when computing interpolant.");
    }
    else
    {
      out_I = Term(new MsatTerm(env, itp));
      return true;
    }
  }
  else if (res == MSAT_SAT)
  {
    return false;
  }
  else
  {
    throw InternalSolverException("Failed when computing interpolant.");
  }
}

// end MsatInterpolatingSolver implementation

}  // namespace smt
