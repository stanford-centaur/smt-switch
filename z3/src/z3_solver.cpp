#include "z3_solver.h"

#include <inttypes.h>
#include <z3++.h>

#include "solver_utils.h"

#include <iostream>

// TEMP for conversions, e.g. creating bit-vectors from base 2 or base 16
// TODO look deeper into Z3 API to see if there's dedicated support
//      Note: there is one for base 2 but not an obvious one for base 16
#include "gmpxx.h"

using namespace std;

namespace smt {

/* Z3 Op mappings */
typedef Z3_ast (*un_fun)(Z3_context c, Z3_ast a);
typedef Z3_ast (*bin_fun)(Z3_context c, Z3_ast t1, Z3_ast t2);
typedef Z3_ast (*tern_fun)(Z3_context c, Z3_ast t1, Z3_ast t2, Z3_ast t3);
typedef Z3_ast (*variadic_fun)(Z3_context c, unsigned num, Z3_ast const args[]);

// extension function
Z3_ast ext_Z3_mk_bvcomp(Z3_context c, Z3_ast t1, Z3_ast t2)
{
  Z3_ast eq = Z3_mk_eq(c, t1, t2);
  Z3_sort bvsort1 = Z3_mk_bv_sort(c, 1);
  Z3_ast one = Z3_mk_unsigned_int(c, 1, bvsort1);
  Z3_ast zero = Z3_mk_unsigned_int(c, 0, bvsort1);
  return Z3_mk_ite(c, eq, one, zero);
}

const std::unordered_map<PrimOp, un_fun> unary_ops(
    { { Not, Z3_mk_not },
      { Negate, Z3_mk_unary_minus },
      { Abs, Z3_mk_fpa_abs },
      { To_Real, Z3_mk_fpa_to_real },
      { To_Int, Z3_mk_str_to_int },
      { Is_Int, Z3_mk_is_int },
      { BVNot, Z3_mk_bvnot },
      { BVNeg, Z3_mk_bvneg } });

const unordered_map<PrimOp, bin_fun> binary_ops({
    { Xor, Z3_mk_xor },
    { Implies, Z3_mk_implies },
    { Pow, Z3_mk_power },
    { IntDiv, Z3_mk_div },
    { Div, Z3_mk_div },
    { Lt, Z3_mk_lt },
    { To_Int, Z3_mk_fpa_round_to_integral },
    { Le, Z3_mk_le },
    { Gt, Z3_mk_gt },
    { Ge, Z3_mk_ge },
    { Equal, Z3_mk_eq },
    { Mod, Z3_mk_mod },
    { Concat, Z3_mk_concat },
    { BVComp, ext_Z3_mk_bvcomp },
    { BVAnd, Z3_mk_bvand },
    { BVOr, Z3_mk_bvor },
    { BVXor, Z3_mk_bvxor },
    { BVNand, Z3_mk_bvnand },
    { BVNor, Z3_mk_bvnor },
    { BVXnor, Z3_mk_bvxnor },
    { BVAdd, Z3_mk_bvadd },
    { BVSub, Z3_mk_bvsub },
    { BVMul, Z3_mk_bvmul },
    { BVUdiv, Z3_mk_bvudiv },
    { BVUrem, Z3_mk_bvurem },
    { BVSdiv, Z3_mk_bvsdiv },
    { BVSrem, Z3_mk_bvsrem },
    { BVSmod, Z3_mk_bvsmod },
    { BVShl, Z3_mk_bvshl },
    { BVAshr, Z3_mk_bvashr },
    { BVLshr, Z3_mk_bvlshr },
    { BVUlt, Z3_mk_bvult },
    { BVUle, Z3_mk_bvule },
    { BVUgt, Z3_mk_bvugt },
    { BVUge, Z3_mk_bvuge },
    { BVSle, Z3_mk_bvsle },
    { BVSlt, Z3_mk_bvslt },
    { BVSge, Z3_mk_bvsge },
    { BVSgt, Z3_mk_bvsgt },
    { Rotate_Left, Z3_mk_ext_rotate_left },
    { Rotate_Right, Z3_mk_ext_rotate_right },
    { Select, Z3_mk_select },

});

const unordered_map<PrimOp, tern_fun> ternary_ops({ { Ite, Z3_mk_ite },
                                                    { Store, Z3_mk_store } });

const unordered_map<PrimOp, variadic_fun> z3_variadic_ops({
    { And, Z3_mk_and },
    { Or, Z3_mk_or },
    { Plus, Z3_mk_add },
    { Minus, Z3_mk_sub },
    { Mult, Z3_mk_mul },
    { Distinct, Z3_mk_distinct },
});

/* Z3Solver implementation */

void Z3Solver::set_opt(const std::string option, const std::string value)
{
  const char * o = option.c_str();
  const char * v = value.c_str();

  // READ PLEASE
  // The easiest handling of Z3's set function's param requirements is to have
  // vectors with the names of different options in the list correspoinding with
  // which param the z3 api expects, it's worth discussing what options we think
  // should go in these lists to start and obviously it is very easy to add more
  // down the line
  unordered_set<string> bool_opts = { "produce-proofs" };
  unordered_set<string> string_opts = {};
  unordered_set<string> int_opts = {};

  if (option == "incremental")
  {
    if (value == "false")
    {
      throw IncorrectUsageException(
          "Z3 backend is always incremental -- it cannot be disabled.");
    }
  }
  else if (option == "produce-models")
  {
    if (value == "true")
    {
      slv.set("model", true);
    }
    else if (value == "false")
    {
      slv.set("model", false);
    }
    else
    {
      throw IncorrectUsageException(
          "produce-models takes values true or false");
    }
  }
  else if (bool_opts.find(option) != bool_opts.end())
  {
    if (value == "true")
    {
      slv.set(o, true);
    }
    else if (value == "false")
    {
      slv.set(o, false);
    }
    else
    {
      throw IncorrectUsageException("Expected a boolean value.");
    }
  }
  else if (string_opts.find(option) != string_opts.end())
  {
    slv.set(o, v);
  }
  else if (int_opts.find(option) != int_opts.end())
  {
    try
    {
      double num = stoi(value, nullptr, 10);
      slv.set(o, num);
    }
    catch (z3::exception & err)
    {
      throw IncorrectUsageException("Expected an integer value.");
    }
  }
  else
  {
    std::string msg("Option - ");
    msg += option;
    msg += " - not implemented for Z3 backend.";
    throw NotImplementedException(msg.c_str());
  }
}

void Z3Solver::set_logic(const std::string logic)
{
  const char * l = logic.c_str();
  slv = solver(ctx, l);
}

Term Z3Solver::make_term(bool b) const
{
  expr z_term = ctx.bool_val(false);
  if (b)
  {
    z_term = ctx.bool_val(true);
  }

  return std::make_shared<Z3Term>(z_term, ctx);
}

Sort Z3Solver::make_sort(const DatatypeDecl & d) const
{
  throw NotImplementedException("Z3Solver::make_sort");
};
DatatypeDecl Z3Solver::make_datatype_decl(const std::string & s)
{
  throw NotImplementedException("Z3Solver::make_datatype_decl");
}
DatatypeConstructorDecl Z3Solver::make_datatype_constructor_decl(
    const std::string s)
{
  throw NotImplementedException("Z3Solver::make_datatype_constructor_decl");
};
void Z3Solver::add_constructor(DatatypeDecl & dt,
                               const DatatypeConstructorDecl & con) const
{
  throw NotImplementedException("Z3Solver::add_constructor");
};
void Z3Solver::add_selector(DatatypeConstructorDecl & dt,
                            const std::string & name,
                            const Sort & s) const
{
  throw NotImplementedException("Z3Solver::add_selector");
};
void Z3Solver::add_selector_self(DatatypeConstructorDecl & dt,
                                 const std::string & name) const
{
  throw NotImplementedException("Z3Solver::add_selector_self");
};

Term Z3Solver::get_constructor(const Sort & s, std::string name) const
{
  throw NotImplementedException("Z3Solver::get_constructor");
};
Term Z3Solver::get_tester(const Sort & s, std::string name) const
{
  throw NotImplementedException("Z3Solver::get_testeer");
};

Term Z3Solver::get_selector(const Sort & s,
                            std::string con,
                            std::string name) const
{
  throw NotImplementedException("Z3Solver::get_selector");
};

Term Z3Solver::make_term(int64_t i, const Sort & sort) const
{
  SortKind sk = sort->get_sort_kind();
  expr z_term = expr(ctx);
  if (sk == INT)
  {
    z_term = ctx.int_val(i);
  }
  else if (sk == REAL)
  {
    z_term = ctx.real_val(i);
  }
  else if (sk == BV)
  {
    z_term = ctx.bv_val(i, sort->get_width());
  }
  else
  {
    string msg("Can't create value ");
    msg += i;
    msg += " with sort ";
    msg += sort->to_string();
    throw IncorrectUsageException(msg);
  }

  return std::make_shared<Z3Term>(z_term, ctx);
}

Term Z3Solver::make_term(const std::string val,
                         const Sort & sort,
                         uint64_t base) const
{
  expr z_term = expr(ctx);
  SortKind sk = sort->get_sort_kind();

  if (base != 10 && sk != BV)
  {
    throw NotImplementedException(
        "Does not support base not equal to 10 for arithmetic.");
  }

  if (sk == BV)
  {
    if (base == 10)
    {
      z_term = ctx.bv_val(val.c_str(), sort->get_width());
    }
    else if (base == 2)
    {
      assert(val.length() == sort->get_width());
      mpz_class value(val, 2);
      z_term = ctx.bv_val(value.get_str(10).c_str(), sort->get_width());
    }
    else if (base == 16)
    {
      mpz_class value(val, 16);
      z_term = ctx.bv_val(value.get_str(10).c_str(), sort->get_width());
    }
    else
    {
      throw IncorrectUsageException("Unsupported base " + std::to_string(base));
    }
  }
  else if (sk == REAL)
  {
    z_term = ctx.real_val(val.c_str());
  }
  else if (sk == INT)
  {
    z_term = ctx.int_val(val.c_str());
  }
  else
  {
    string msg("Can't create value ");
    msg += val;
    msg += " with sort ";
    msg += sort->to_string();
    throw IncorrectUsageException(msg);
  }

  return std::make_shared<Z3Term>(z_term, ctx);
}

Term Z3Solver::make_term(const Term & val, const Sort & sort) const
{
  std::shared_ptr<Z3Term> zterm = std::static_pointer_cast<Z3Term>(val);
  std::shared_ptr<Z3Sort> zsort = std::static_pointer_cast<Z3Sort>(sort);

  if (zsort->is_function || zterm->is_function)
  {
    throw IncorrectUsageException(
        "Cannot create constant array with function element");
  }
  z3::sort arrtype = zsort->type;
  assert(arrtype.is_array());

  Z3_ast c_array = Z3_mk_const_array(ctx, arrtype.array_domain(), zterm->term);
  expr final = to_expr(ctx, c_array);
  return std::make_shared<Z3Term>(final, ctx);
}

void Z3Solver::assert_formula(const Term & t)
{
  std::shared_ptr<Z3Term> zterm = std::static_pointer_cast<Z3Term>(t);
  if (zterm->is_function)
  {
    throw IncorrectUsageException(
        "Attempted to assert a function directly to solver");
  }
  slv.add(zterm->term);
}

Result Z3Solver::check_sat()
{
  check_result r = slv.check();
  if (r == unsat)
  {
    return Result(UNSAT);
  }
  else if (r == sat)
  {
    return Result(SAT);
  }
  else if (r == unknown)
  {
    return Result(UNKNOWN, slv.reason_unknown());
  }
  else
  {
    throw NotImplementedException("Unimplemented result type from Z3");
  }
}

Result Z3Solver::check_sat_assuming(const TermVec & assumptions)
{
  z3::expr_vector z3assumps(ctx);

  shared_ptr<Z3Term> za;
  for (auto a : assumptions)
  {
    za = static_pointer_cast<Z3Term>(a);
    if (za->is_function)
    {
      throw IncorrectUsageException(
          "Functions cannot be used directly as assumptions.");
    }
    z3assumps.push_back(za->term);
  }

  return check_sat_assuming(z3assumps);
}

Result Z3Solver::check_sat_assuming_list(const TermList & assumptions)
{
  z3::expr_vector z3assumps(ctx);

  shared_ptr<Z3Term> za;
  for (auto a : assumptions)
  {
    za = static_pointer_cast<Z3Term>(a);
    if (za->is_function)
    {
      throw IncorrectUsageException(
          "Functions cannot be used directly as assumptions.");
    }
    z3assumps.push_back(za->term);
  }

  return check_sat_assuming(z3assumps);
}

Result Z3Solver::check_sat_assuming_set(const UnorderedTermSet & assumptions)
{
  z3::expr_vector z3assumps(ctx);

  shared_ptr<Z3Term> za;
  for (auto a : assumptions)
  {
    za = static_pointer_cast<Z3Term>(a);
    if (za->is_function)
    {
      throw IncorrectUsageException(
          "Functions cannot be used directly as assumptions.");
    }
    z3assumps.push_back(za->term);
  }

  return check_sat_assuming(z3assumps);
}

void Z3Solver::push(uint64_t num)
{
  for (int i = 0; i < num; i++)
  {
    slv.push();
  }
  context_level += num;
}

void Z3Solver::pop(uint64_t num)
{
  slv.pop(num);
  context_level -= num;
}

uint64_t Z3Solver::get_context_level() const { return context_level; }

Term Z3Solver::get_value(const Term & t) const
{
  shared_ptr<Z3Term> zterm = static_pointer_cast<Z3Term>(t);
  if (zterm->is_function)
  {
    throw IncorrectUsageException("Cannot evaluate a function.");
  }
  z3::model model = slv.get_model();
  expr eval = model.eval(zterm->term, true);
  return std::make_shared<Z3Term>(eval, ctx);
}

UnorderedTermMap Z3Solver::get_array_values(const Term & arr,
                                            Term & out_const_base) const
{
  throw NotImplementedException(
      "Get array values not implemented for Z3 backend.");
}

void Z3Solver::get_unsat_assumptions(UnorderedTermSet & out)
{
  throw NotImplementedException(
      "Get unsat core not implemented for Z3 backend.");
}

Sort Z3Solver::make_sort(const std::string name, uint64_t arity) const
{
  if (!arity)
  {
    const char * c = name.c_str();
    z3::symbol func_name = ctx.str_symbol(c);
    z3::sort z_sort = ctx.uninterpreted_sort(func_name);
    return std::make_shared<Z3Sort>(z_sort, ctx);
  }
  else
  {
    throw NotImplementedException(
        "Z3 does not support uninterpreted type with non-zero arity.");
  }
}

Sort Z3Solver::make_sort(SortKind sk) const
{
  z3::sort z_sort = z3::sort(ctx);

  if (sk == BOOL)
  {
    z_sort = ctx.bool_sort();
  }
  else if (sk == INT)
  {
    z_sort = ctx.int_sort();
  }
  else if (sk == REAL)
  {
    z_sort = ctx.real_sort();
  }
  else
  {
    std::string msg("Can't create sort with sort constructor ");
    msg += to_string(sk);
    msg += " and no arguments";
    throw IncorrectUsageException(msg.c_str());
  }

  Sort final_sort = std::make_shared<Z3Sort>(z_sort, ctx);
  return final_sort;
}

Sort Z3Solver::make_sort(SortKind sk, uint64_t size) const
{
  if (sk == BV)
  {
    return std::make_shared<Z3Sort>(ctx.bv_sort(size), ctx);
  }
  else
  {
    std::string msg("Can't create sort with sort constructor ");
    msg += to_string(sk);
    msg += " and an integer argument";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort Z3Solver::make_sort(SortKind sk, const Sort & sort1) const
{
  throw NotImplementedException(
      "Smt-switch does not have any sorts that take one sort parameter yet.");
}

Sort Z3Solver::make_sort(SortKind sk,
                         const Sort & sort1,
                         const Sort & sort2) const
{
  if (sk == ARRAY)
  {
    std::shared_ptr<Z3Sort> cidxsort = std::static_pointer_cast<Z3Sort>(sort1);
    std::shared_ptr<Z3Sort> celemsort = std::static_pointer_cast<Z3Sort>(sort2);
    return std::make_shared<Z3Sort>(
        ctx.array_sort(cidxsort->type, celemsort->type), ctx);
  }
  else
  {
    std::string msg("Can't create sort with sort constructor ");
    msg += to_string(sk);
    msg += " and two Sort arguments";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort Z3Solver::make_sort(SortKind sk,
                         const Sort & sort1,
                         const Sort & sort2,
                         const Sort & sort3) const
{
  throw NotImplementedException(
      "Smt-switch does not have any sorts that take three sort parameters "
      "yet.");
}

Sort Z3Solver::make_sort(SortKind sk, const SortVec & sorts) const
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

    std::vector<z3::sort> zsorts;
    zsorts.reserve(arity);
    z3::sort z_sort = z3::sort(ctx);

    for (uint32_t i = 0; i < arity; i++)
    {
      z_sort = std::static_pointer_cast<Z3Sort>(sorts[i])->type;
      zsorts.push_back(z_sort);
    }

    Sort sort = sorts.back();
    z_sort = std::static_pointer_cast<Z3Sort>(sort)->type;

    const char * c = "throwaway name";
    z3::symbol func_name = ctx.str_symbol(c);
    z3::func_decl z_func = ctx.function(func_name, arity, &zsorts[0], z_sort);

    return std::make_shared<Z3Sort>(z_func, ctx);
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

Sort Z3Solver::make_sort(const Sort & sort_con, const SortVec & sorts) const
{
  throw NotImplementedException(
      "Z3 does not support uninterpreted sort constructors");
}

Term Z3Solver::make_symbol(const std::string name, const Sort & sort)
{
  if (symbol_table.find(name) != symbol_table.end())
  {
    throw IncorrectUsageException("symbol " + name + " has already been used.");
  }

  shared_ptr<Z3Sort> zsort = static_pointer_cast<Z3Sort>(sort);
  const char * c = name.c_str();
  z3::symbol z_name = ctx.str_symbol(c);

  Term sym;
  if (zsort->get_sort_kind() == FUNCTION)
  {
    // nb this is creating a func_decl
    func_decl sort_func = zsort->z_func;

    sort_vector domain(ctx);
    for (int i = 0; i < sort_func.arity(); i++)
    {
      domain.push_back(sort_func.domain(i));
    }

    func_decl z_func = ctx.function(c, domain, sort_func.range());
    sym = std::make_shared<Z3Term>(z_func, ctx);
  }
  else
  {
    // nb this is creating an expr
    expr z_term = ctx.constant(z_name, zsort->type);

    sym = std::make_shared<Z3Term>(z_term, ctx);
  }
  assert(sym);
  symbol_table[name] = sym;
  return sym;
}

Term Z3Solver::get_symbol(const std::string & name)
{
  auto it = symbol_table.find(name);
  if (it == symbol_table.end())
  {
    throw IncorrectUsageException("Symbol named " + name + " does not exist.");
  }
  return it->second;
}

Term Z3Solver::make_param(const std::string name, const Sort & sort)
{
  shared_ptr<Z3Sort> zsort = static_pointer_cast<Z3Sort>(sort);
  const char * c = name.c_str();
  z3::symbol z_name = ctx.str_symbol(c);

  if (zsort->is_function)
  {
    throw IncorrectUsageException("Functions cannot be parameters");
  }

  expr z_term = ctx.constant(z_name, zsort->type);
  // mark as a parameter by passing true
  return std::make_shared<Z3Term>(z_term, ctx, true);
}

Term Z3Solver::make_term(Op op, const Term & t) const
{
  shared_ptr<Z3Term> zterm = static_pointer_cast<Z3Term>(t);
  Z3_ast res;

  if (zterm->is_function)
  {
    throw IncorrectUsageException(
        "Cannot make a unary operator term with a function.");
  }

  if (op.prim_op == Extract)
  {
    if (op.idx0 < 0 || op.idx1 < 0)
    {
      throw IncorrectUsageException("Can't have negative number in extract");
    }
    res = Z3_mk_extract(ctx, op.idx0, op.idx1, zterm->term);
  }
  else if (op.prim_op == Zero_Extend)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException("Can't zero extend by negative number");
    }
    res = Z3_mk_zero_ext(ctx, op.idx0, zterm->term);
  }
  else if (op.prim_op == Sign_Extend)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException("Can't sign extend by negative number");
    }
    res = Z3_mk_sign_ext(ctx, op.idx0, zterm->term);
  }
  else if (op.prim_op == Repeat)
  {
    if (op.num_idx < 1)
    {
      throw IncorrectUsageException("Can't create repeat with index < 1");
    }
    res = Z3_mk_repeat(ctx, op.idx0, zterm->term);
  }
  else if (op.prim_op == Rotate_Left)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException("Can't rotate by negative number");
    }
    res = Z3_mk_rotate_left(ctx, op.idx0, zterm->term);
  }
  else if (op.prim_op == Rotate_Right)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException("Can't rotate by negative number");
    }
    res = Z3_mk_rotate_right(ctx, op.idx0, zterm->term);
  }
  else if (op.prim_op == Int_To_BV)
  {
    if (op.idx0 < 0)
    {
      throw IncorrectUsageException(
          "Can't have negative width in Int_To_BV op");
    }
    res = Z3_mk_int2bv(ctx, op.idx0, zterm->term);
  }
  else if (op.prim_op == BV_To_Nat)
  {
    // n.b., the third parameter is a boolean is_signed, by flagging it false,
    // this becomes bv2nat
    res = Z3_mk_bv2int(ctx, zterm->term, false);
  }

  else if (!op.num_idx)
  {
    if (unary_ops.find(op.prim_op) != unary_ops.end())
    {
      res = unary_ops.at(op.prim_op)(ctx, zterm->term);
    }
    else
    {
      string msg("Can't apply ");
      msg += op.to_string();
      msg += " to the term or not supported by Z3 backend yet.";
      throw IncorrectUsageException(msg);
    }
  }
  else
  {
    string msg = op.to_string();
    msg += " not supported for one term argument";
    throw IncorrectUsageException(msg);
  }

  return std::make_shared<Z3Term>(to_expr(ctx, res), ctx);
}

Term Z3Solver::make_term(Op op, const Term & t0, const Term & t1) const
{
  shared_ptr<Z3Term> zterm0 = static_pointer_cast<Z3Term>(t0);
  shared_ptr<Z3Term> zterm1 = static_pointer_cast<Z3Term>(t1);
  Z3_ast res;

  if (zterm0->is_function || zterm1->is_function)
  {
    if (op.prim_op == Apply)
    {
      return make_term(op, TermVec{ t0, t1 });
    }
    throw IncorrectUsageException(
        "Cannot make a binary op term with a function.");
  }

  check_context(zterm0->term, zterm1->term);

  if (!op.num_idx)
  {
    if (binary_ops.find(op.prim_op) != binary_ops.end())
    {
      res = binary_ops.at(op.prim_op)(ctx, zterm0->term, zterm1->term);
    }
    else if (z3_variadic_ops.find(op.prim_op) != z3_variadic_ops.end())
    {
      Z3_ast terms[2] = { zterm0->term, zterm1->term };
      res = z3_variadic_ops.at(op.prim_op)(ctx, 2, terms);
    }
    else if (op == Forall || op == Exists)
    {
      z3::expr_vector zparams(ctx);
      zparams.push_back(static_pointer_cast<Z3Term>(t0)->term);
      z3::expr zbody = static_pointer_cast<Z3Term>(t1)->term;
      if (op == Forall)
      {
        return make_shared<Z3Term>(forall(zparams, zbody), ctx);
      }
      else
      {
        assert(op == Exists);
        return make_shared<Z3Term>(exists(zparams, zbody), ctx);
      }
    }
    else
    {
      string msg("Can't apply ");
      msg += op.to_string();
      msg += " to the term or not supported by Z3 backend yet.";
      throw IncorrectUsageException(msg);
    }
  }
  else
  {
    string msg = op.to_string();
    msg += " not supported for two term argument";
    throw IncorrectUsageException(msg);
  }

  return std::make_shared<Z3Term>(to_expr(ctx, res), ctx);
}

Term Z3Solver::make_term(Op op,
                         const Term & t0,
                         const Term & t1,
                         const Term & t2) const
{
  shared_ptr<Z3Term> zterm0 = static_pointer_cast<Z3Term>(t0);
  shared_ptr<Z3Term> zterm1 = static_pointer_cast<Z3Term>(t1);
  shared_ptr<Z3Term> zterm2 = static_pointer_cast<Z3Term>(t2);
  Z3_ast res;

  if (zterm0->is_function || zterm1->is_function || zterm2->is_function)
  {
    if (op.prim_op == Apply)
    {
      return make_term(op, TermVec{ t0, t1, t2 });
    }
    throw IncorrectUsageException(
        "Cannot make a ternary op term with a function.");
  }

  check_context(zterm0->term, zterm1->term);
  check_context(zterm0->term, zterm2->term);

  if (!op.num_idx)
  {
    if (ternary_ops.find(op.prim_op) != ternary_ops.end())
    {
      res = ternary_ops.at(op.prim_op)(
          ctx, zterm0->term, zterm1->term, zterm2->term);
    }
    else if (z3_variadic_ops.find(op.prim_op) != z3_variadic_ops.end())
    {
      Z3_ast terms[3] = { zterm0->term, zterm1->term, zterm2->term };
      res = z3_variadic_ops.at(op.prim_op)(ctx, 3, terms);
    }
    else if (op == Forall || op == Exists)
    {
      z3::expr_vector zparams(ctx);
      zparams.push_back(static_pointer_cast<Z3Term>(t0)->term);
      zparams.push_back(static_pointer_cast<Z3Term>(t1)->term);
      z3::expr zbody = static_pointer_cast<Z3Term>(t2)->term;
      if (op == Forall)
      {
        return make_shared<Z3Term>(forall(zparams, zbody), ctx);
      }
      else
      {
        assert(op == Exists);
        return make_shared<Z3Term>(exists(zparams, zbody), ctx);
      }
    }
    else
    {
      string msg("Can't apply ");
      msg += op.to_string();
      msg += " to three terms, or not supported by Z3 backend yet.";
      throw IncorrectUsageException(msg);
    }
  }
  else
  {
    string msg = op.to_string();
    msg += " not supported for three term arguments";
    throw IncorrectUsageException(msg);
  }

  return std::make_shared<Z3Term>(to_expr(ctx, res), ctx);
}

Term Z3Solver::make_term(Op op, const TermVec & terms) const
{
  size_t size = terms.size();
  Z3_ast res;

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

  if (op.prim_op == Apply)
  {
    vector<Z3_ast> zargs;
    zargs.reserve(size - 1);
    shared_ptr<Z3Term> zterm;

    // skip the first term (the function function)
    for (size_t i = 1; i < terms.size(); i++)
    {
      zterm = static_pointer_cast<Z3Term>(terms[i]);
      if (zterm->is_function)
      {
        throw IncorrectUsageException("Cannot use a function as an argument.");
      }
      zargs.push_back(zterm->term);
    }

    zterm = static_pointer_cast<Z3Term>(terms[0]);
    if (!zterm->is_function)
    {
      string msg(
          "Expecting an uninterpreted function to be used with Apply but got ");
      msg += terms[0]->to_string();
      throw IncorrectUsageException(msg);
    }

    res = Z3_mk_app(ctx, zterm->z_func, size - 1, &zargs[0]);
    return std::make_shared<Z3Term>(to_expr(ctx, res), ctx);
  }

  if (op.prim_op == Forall || op.prim_op == Exists)
  {
    z3::expr_vector zterms(ctx);
    std::shared_ptr<Z3Term> zterm;
    for (auto t : terms)
    {
      zterm = std::static_pointer_cast<Z3Term>(t);
      if (zterm->is_function)
      {
        throw IncorrectUsageException(
            "quantifiers with functions not supported.");
      }
      zterms.push_back(zterm->term);
    }
    expr quantified_body = zterms.back();
    zterms.pop_back();
    unsigned num_var = zterms.size();  // this will always be one when only
                                       // allowing one parameter

    z3::expr quant_res(ctx);
    if (op.prim_op == Forall)
    {
      quant_res = forall(zterms, quantified_body);
    }
    if (op.prim_op == Exists)
    {
      quant_res = exists(zterms, quantified_body);
    }
    return std::make_shared<Z3Term>(quant_res, ctx);
  }

  if (size == 2)
  {
    return make_term(op, terms[0], terms[1]);
  }
  else if (size == 3 && ternary_ops.find(op.prim_op) != ternary_ops.end())
  {
    return make_term(op, terms[0], terms[1], terms[2]);
  }
  else if (is_variadic(op.prim_op))
  {
    std::vector<Z3_ast> z3args;
    z3args.reserve(size);
    for (const auto & tt : terms)
    {
      z3args.push_back(std::static_pointer_cast<Z3Term>(tt)->term);
    }

    Z3_ast res;
    if (z3_variadic_ops.find(op.prim_op) != z3_variadic_ops.end())
    {
      res = z3_variadic_ops.at(op.prim_op)(ctx, z3args.size(), z3args.data());
    }
    else
    {
      // assume this is a binary operator extended to n arguments
      auto z3_fun = binary_ops.at(op.prim_op);
      res = z3_fun(ctx, z3args[0], z3args[1]);
      for (size_t i = 2; i < size; ++i)
      {
        res = z3_fun(ctx, res, z3args[i]);
      }
    }
    return std::make_shared<Z3Term>(to_expr(ctx, res), ctx);
  }
  else if (op == Distinct)
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

void Z3Solver::reset() { slv.reset(); }

void Z3Solver::reset_assertions() { slv.reset(); }

Term Z3Solver::substitute(const Term term,
                          const UnorderedTermMap & substitution_map) const
{
  // z3 expression vectors that represent the
  // substitution map, i.e.:
  // substitutionmap[z3sources[i]] = z3destinations[i]
  z3::expr_vector z3sources(ctx);
  z3::expr_vector z3destinations(ctx);

  // z3 counterpart of `term`
  shared_ptr<Z3Term> z3term = static_pointer_cast<Z3Term>(term);
  expr z3expr = to_expr(ctx, z3term->term);
  // populate the z3 expr_vectors according to the substitution map
  for (auto p : substitution_map)
  {
    Term from_term = p.first;
    Term to_term = p.second;
    shared_ptr<Z3Term> z3_from_term = static_pointer_cast<Z3Term>(from_term);
    shared_ptr<Z3Term> z3_to_term = static_pointer_cast<Z3Term>(to_term);
    z3sources.push_back(z3_from_term->term);
    z3destinations.push_back(z3_to_term->term);
  }

  // perform the substitution and return the result
  expr result = z3expr.substitute(z3sources, z3destinations);
  return std::make_shared<Z3Term>(result, ctx);
}

void Z3Solver::dump_smt2(std::string filename) const
{
  throw NotImplementedException("Dumping smt2 not supported by Z3 backend.");
}

/* end Z3Solver implementation */

}  // namespace smt
