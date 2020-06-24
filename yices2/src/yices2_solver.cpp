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

#include <inttypes.h>

#include "yices.h"
#include "yices2_extensions.h"

using namespace std;

namespace smt {

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
    { { And, yices_and2 },          { Or, yices_or2 },
      { Xor, yices_xor2 },          { Implies, yices_implies },
      { Iff, yices_iff },           { Plus, yices_add },
      { Minus, yices_sub },         { Mult, yices_mul },
      { Div, yices_division },      { Lt, yices_arith_lt_atom },
      { IntDiv, yices_idiv },       { Le, yices_arith_leq_atom },
      { Gt, yices_arith_gt_atom },  { Ge, yices_arith_geq_atom },
      { Equal, yices_eq },          { Mod, yices_imod },
      { Concat, yices_bvconcat2 },  { BVAnd, yices_bvand2 },
      { BVOr, yices_bvor2 },        { BVXor, yices_bvxor2 },
      { BVNand, yices_bvnand },     { BVNor, yices_bvnor },
      { BVXnor, yices_bvxnor },     { BVAdd, yices_bvadd },
      { BVSub, yices_bvsub },       { BVMul, yices_bvmul },
      { BVUdiv, yices_bvdiv },      { BVUrem, yices_bvrem },
      { BVSdiv, yices_bvsdiv },     { BVSrem, yices_bvsrem },
      { BVSmod, yices_bvsmod },     { BVShl, yices_bvshl },
      { BVAshr, yices_bvashr },     { BVLshr, yices_bvlshr },
      { BVUlt, yices_bvlt_atom },   { BVUle, yices_bvle_atom },
      { BVUgt, yices_bvgt_atom },   { BVUge, yices_bvge_atom },
      { BVSle, yices_bvsle_atom },  { BVSlt, yices_bvslt_atom },
      { BVSge, yices_bvsge_atom },  { BVSgt, yices_bvsgt_atom },
      { Select, ext_yices_select }, { Apply, yices_application1 }

    });

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
    if (value == "false")
    {
      yices_set_config(config, "mode", "one-shot");
    }
    else if (value == "true")
    {
      yices_set_config(config, "mode", "push-pop");
    }
  }
  else if (option == "produce-unsat-cores")
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
  ctx = yices_new_context(config);
}

void Yices2Solver::set_logic(const std::string logic)
{
  yices_default_config_for_logic(config, logic.c_str());
  ctx = yices_new_context(config);
  // TODO: Does this enforce an ordering of calling set_logic before set_opt.
  // Need to decide on a better place to put the context creation.
  // yices_free_config(config);
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

  return std::make_shared<Yices2Term> (y_term);
}


Sort Yices2Solver::make_sort(const DatatypeDecl & d) const {
  throw NotImplementedException("Yices2Solver::make_sort");
};
DatatypeDecl Yices2Solver::make_datatype_decl(const std::string & s)  {
    throw NotImplementedException("Yices2Solver::make_datatype_decl");
}
DatatypeConstructorDecl Yices2Solver::make_datatype_constructor_decl(
    const std::string s)
{
  throw NotImplementedException("Yices2Solver::make_datatype_constructor_decl");
};
void Yices2Solver::add_constructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const {
  throw NotImplementedException("Yices2Solver::add_constructor");
};
void Yices2Solver::add_selector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const {
  throw NotImplementedException("Yices2Solver::add_selector");
};
void Yices2Solver::add_selector_self(DatatypeConstructorDecl & dt, const std::string & name) const {
  throw NotImplementedException("Yices2Solver::add_selector_self");
};

Term Yices2Solver::get_constructor(const Sort & s, std::string name) const  {
  throw NotImplementedException("Yices2Solver::get_constructor");
};
Term Yices2Solver::get_tester(const Sort & s, std::string name) const  {
  throw NotImplementedException("Yices2Solver::get_testeer");
};

Term Yices2Solver::get_selector(const Sort & s, std::string con, std::string name) const  {
  throw NotImplementedException("Yices2Solver::get_selector");
};


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

  return std::make_shared<Yices2Term> (y_term);
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

    y_term = yices_parse_float(val.c_str());
  }
  else if (sk == INT)
  {
    int i = stoi(val);
    y_term = yices_int64(i);
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

  return std::make_shared<Yices2Term> (y_term);
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

  int32_t my_error = yices_assert_formula(ctx, yterm->term);
  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }
}

Result Yices2Solver::check_sat()
{
  smt_status_t res = yices_check_context(ctx, NULL);

  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }

  if (res == STATUS_SAT)
  {
    return Result(SAT);
  }
  else if (res == STATUS_UNSAT)
  {
    return Result(UNSAT);
  }
  else
  {
    return Result(UNKNOWN);
  }
}

Result Yices2Solver::check_sat_assuming(const TermVec & assumptions)
{
  // expecting (possibly negated) boolean literals
  for (auto a : assumptions)
  {
    if (a->get_sort()->get_sort_kind() != BOOL)
    {
      throw IncorrectUsageException(
          "Cannot assume a term with sort other than BOOL.");
    }
    else if (!a->is_symbolic_const())
    {
      shared_ptr<Yices2Term> yt = static_pointer_cast<Yices2Term>(a);
      term_constructor_t tc = yices_term_constructor(yt->term);
      if (tc == YICES_NOT_TERM && yices_term_num_children(yt->term) == 1
          && yices_term_constructor(yices_term_child(yt->term, 0))
                 == YICES_UNINTERPRETED_TERM
          && yices_term_num_children(yices_term_child(yt->term, 0)) == 0)
      {
        // this is a negated boolean literal
        continue;
      }
      else
      {
        throw IncorrectUsageException(
            "Expecting boolean indicator literals but got: " + a->to_string());
      }
    }
  }

  vector<term_t> y_assumps;
  y_assumps.reserve(assumptions.size());

  shared_ptr<Yices2Term> ya;
  for (auto a : assumptions)
  {
    ya = static_pointer_cast<Yices2Term>(a);
    y_assumps.push_back(ya->term);
  }

  smt_status_t res = yices_check_context_with_assumptions(
      ctx, NULL, y_assumps.size(), &y_assumps[0]);

  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }

  if (res == STATUS_SAT)
  {
    return Result(SAT);
  }
  else if (res == STATUS_UNSAT)
  {
    return Result(UNSAT);
  }
  else
  {
    return Result(UNKNOWN);
  }
}

void Yices2Solver::push(uint64_t num) { yices_push(ctx); }

void Yices2Solver::pop(uint64_t num) { yices_pop(ctx); }

Term Yices2Solver::get_value(const Term & t) const
{
  shared_ptr<Yices2Term> yterm = static_pointer_cast<Yices2Term>(t);
  model_t * model = yices_get_model(ctx, true);

  if (!yices_term_is_function(yterm->term))
  {
    return std::make_shared<Yices2Term>
        (yices_get_value_as_term(model, yterm->term));
  }
  else
  {
    throw NotImplementedException(
        "Yices does not support get-value for arrays.");
  }
}

UnorderedTermMap Yices2Solver::get_array_values(const Term & arr,
                                                Term & out_const_base) const
{
  throw NotImplementedException(
      "Yices does not support getting array values. Please use get_value on a "
      "particular select of the array.");
}

TermVec Yices2Solver::get_unsat_core()
{
  term_vector_t ycore;
  yices_init_term_vector(&ycore);
  int32_t err_code = yices_get_unsat_core(ctx, &ycore);
  // yices2 documentation: returns -1 if ctx status was not UNSAT
  if (err_code == -1)
  {
    throw IncorrectUsageException(
        "Last call to check_sat was not unsat, cannot get unsat core.");
  }

  TermVec core;
  for (size_t i = 0; i < ycore.size; ++i)
  {
    if (!ycore.data[i])
    {
      throw InternalSolverException("Got an empty term from vector");
    }
    core.push_back(std::make_shared<Yices2Term>(ycore.data[i]));
  }

  yices_delete_term_vector(&ycore);

  return core;
}

Sort Yices2Solver::make_sort(const std::string name, uint64_t arity) const
{
  type_t y_sort;

  if (!arity)
  {
    y_sort = yices_new_uninterpreted_type();
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

  return std::make_shared<Yices2Sort> (y_sort);
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

  return std::make_shared<Yices2Sort> (y_sort);
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

Sort Yices2Solver::make_sort(SortKind sk, const Sort & sort1) const
{
  throw NotImplementedException(
      "Smt-switch does not have any sorts that take one sort parameter yet.");
}

Sort Yices2Solver::make_sort(SortKind sk,
                             const Sort & sort1,
                             const Sort & sort2) const
{
  std::shared_ptr<Yices2Sort> s1 = std::static_pointer_cast<Yices2Sort>(sort1);
  std::shared_ptr<Yices2Sort> s2 = std::static_pointer_cast<Yices2Sort>(sort2);
  Sort ret_sort;

  if (sk == ARRAY)
  {
    ret_sort = std::make_shared<Yices2Sort>
        (yices_function_type1(s1->type, s2->type));
  }
  else if (sk == FUNCTION)
  {
    ret_sort = std::make_shared<Yices2Sort>
        (yices_function_type1(s1->type, s2->type), true);
  }
  else
  {
    std::string msg("Can't create sort with sort constructor ");
    msg += to_string(sk);
    msg += " and two Sort arguments";
    throw IncorrectUsageException(msg.c_str());
  }

  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }

  return ret_sort;
}

Sort Yices2Solver::make_sort(SortKind sk,
                             const Sort & sort1,
                             const Sort & sort2,
                             const Sort & sort3) const
{
  throw NotImplementedException(
      "Smt-switch does not have any sorts that take three sort parameters "
      "yet.");
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

  if (yices_error_code() != 0)
  {
    std::string msg(yices_error_string());
    throw InternalSolverException(msg.c_str());
  }

  return std::make_shared<Yices2Sort> (y_sort, true);
}

Term Yices2Solver::make_symbol(const std::string name, const Sort & sort)
{
  shared_ptr<Yices2Sort> ysort = static_pointer_cast<Yices2Sort>(sort);
  term_t y_term = yices_new_uninterpreted_term(ysort->type);
  yices_set_term_name(y_term, name.c_str());

  if (ysort->get_sort_kind() == FUNCTION)
  {
    return std::make_shared<Yices2Term> (y_term, true);
  }

  return std::make_shared<Yices2Term> (y_term);
}

Term Yices2Solver::make_term(Op op, const Term & t) const
{
  shared_ptr<Yices2Term> yterm = static_pointer_cast<Yices2Term>(t);
  term_t res;

  if (op.prim_op == Extract)
  {
    if (op.idx0 < 0 || op.idx1 < 0)
    {
      throw IncorrectUsageException("Can't have negative number in extract");
    }
    res = yices_bvextract(yterm->term, op.idx1, op.idx0);
  }
  else if (op.prim_op == Zero_Extend)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException("Can't zero extend by negative number");
    }
    res = yices_zero_extend(yterm->term, op.idx0);
  }
  else if (op.prim_op == Sign_Extend)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException("Can't sign extend by negative number");
    }
    res = yices_sign_extend(yterm->term, op.idx0);
  }
  else if (op.prim_op == Repeat)
  {
    if (op.num_idx < 1)
    {
      throw IncorrectUsageException("Can't create repeat with index < 1");
    }
    res = yices_bvrepeat(yterm->term, op.idx0);
  }
  else if (op.prim_op == Rotate_Left)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException("Can't rotate by negative number");
    }
    res = yices_rotate_left(yterm->term, op.idx0);
  }
  else if (op.prim_op == Rotate_Right)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException("Can't rotate by negative number");
    }
    res = yices_rotate_right(yterm->term, op.idx0);
  }
  else if (op.prim_op == Int_To_BV)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException(
          "Can't have negative width in Int_To_BV op");
    }
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

  return std::make_shared<Yices2Term> (res);
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
    return std::make_shared<Yices2Term> (res, true);
  }
  else
  {
    return std::make_shared<Yices2Term> (res);
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
    return std::make_shared<Yices2Term> (res, true);
  }
  else
  {
    return std::make_shared<Yices2Term> (res);
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
  else if (size == 3)
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
  // else if() ... check the variadic terms list.
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

  return std::make_shared<Yices2Term> (res);
}

void Yices2Solver::reset()
{
  yices_reset();
  // call this with NULL or config?
  ctx = yices_new_context(NULL);
}

void Yices2Solver::reset_assertions() { yices_reset_context(ctx); }

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

  return std::make_shared<Yices2Term> (res);
}

void Yices2Solver::dump_smt2(std::string filename) const
{
  throw NotImplementedException(
      "Dumping smt2 not supported by Yices2 backend.");
}

/* end Yices2Solver implementation */

}  // namespace smt
