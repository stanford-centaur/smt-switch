#include "z3_solver.h"

#include <z3++.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <memory>
#include <string>
#include <type_traits>
#include <unordered_set>
#include <utility>
#include <vector>

#include "datatype.h"
#include "exceptions.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver_enums.h"
#include "solver_utils.h"
#include "sort.h"
#include "utils.h"
#include "z3_datatype.h"
#include "z3_sort.h"
#include "z3_term.h"

using namespace std;

namespace smt {

// The narrowing helpers return a std::uint32_t, which Z3 takes as unsigned.
static_assert(std::is_same_v<unsigned, std::uint32_t>,
              "Z3 takes counts and widths as an unsigned of 32 bits");

// extension function: bvcomp as an ite over equality. Each new term is
// referenced until the ite holds it, as in ext_Z3_mk_abs.
Z3_ast ext_Z3_mk_bvcomp(Z3_context c, Z3_ast t1, Z3_ast t2)
{
  Z3_ast eq = Z3_mk_eq(c, t1, t2);
  Z3_inc_ref(c, eq);
  Z3_sort bvsort1 = Z3_mk_bv_sort(c, 1);
  Z3_ast one = Z3_mk_unsigned_int(c, 1, bvsort1);
  Z3_inc_ref(c, one);
  Z3_ast zero = Z3_mk_unsigned_int(c, 0, bvsort1);
  Z3_inc_ref(c, zero);
  Z3_ast result = Z3_mk_ite(c, eq, one, zero);
  Z3_dec_ref(c, zero);
  Z3_dec_ref(c, one);
  Z3_dec_ref(c, eq);
  return result;
}

// extension function: the absolute value of an Int or a Real, built from
// ite as Z3's C++ API builds it. The context counts references, so each
// new term is referenced until the ite holds it, or the next call may
// reuse it.
Z3_ast ext_Z3_mk_abs(Z3_context c, Z3_ast a)
{
  Z3_ast zero = Z3_mk_int(c, 0, Z3_get_sort(c, a));
  Z3_inc_ref(c, zero);
  Z3_ast nonnegative = Z3_mk_ge(c, a, zero);
  Z3_inc_ref(c, nonnegative);
  Z3_ast negated = Z3_mk_unary_minus(c, a);
  Z3_inc_ref(c, negated);
  Z3_ast result = Z3_mk_ite(c, nonnegative, a, negated);
  Z3_dec_ref(c, negated);
  Z3_dec_ref(c, nonnegative);
  Z3_dec_ref(c, zero);
  return result;
}

// extension function: the division of Reals. Z3_mk_div divides Ints as Ints,
// so Int arguments are converted to Reals first, and referenced until the
// division holds them.
Z3_ast ext_Z3_mk_real_div(Z3_context c, Z3_ast t1, Z3_ast t2)
{
  Z3_ast args[2] = { t1, t2 };
  for (Z3_ast & arg : args)
  {
    if (Z3_get_sort_kind(c, Z3_get_sort(c, arg)) == Z3_INT_SORT)
    {
      arg = Z3_mk_int2real(c, arg);
    }
    Z3_inc_ref(c, arg);
  }
  Z3_ast result = Z3_mk_div(c, args[0], args[1]);
  Z3_dec_ref(c, args[1]);
  Z3_dec_ref(c, args[0]);
  return result;
}

/** Refuses po applied to num_args arguments, which this backend has no Z3
 *  call for
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
  throw NotImplementedException("The Z3 backend does not support the operator "
                                + to_string(po));
}

/** The term of op applied to one argument
 *  @throws as throw_unsupported where this backend has no such op
 */
static Z3_ast unary_term(Z3_context c, const Op & op, Z3_ast a)
{
  switch (op.prim_op)
  {
    case Not: return Z3_mk_not(c, a);
    case Negate: return Z3_mk_unary_minus(c, a);
    case Abs: return ext_Z3_mk_abs(c, a);
    case To_Real: return Z3_mk_int2real(c, a);
    case To_Int: return Z3_mk_real2int(c, a);
    case Is_Int: return Z3_mk_is_int(c, a);
    case Extract:
      return Z3_mk_extract(c,
                           narrow_index(op, op.indices[0]),
                           narrow_index(op, op.indices[1]),
                           a);
    case BVNot: return Z3_mk_bvnot(c, a);
    case BVNeg: return Z3_mk_bvneg(c, a);
    case Zero_Extend:
      return Z3_mk_zero_ext(c, narrow_index(op, op.indices[0]), a);
    case Sign_Extend:
      return Z3_mk_sign_ext(c, narrow_index(op, op.indices[0]), a);
    case Repeat:
      if (op.indices[0] < 1)
      {
        throw IncorrectUsageException("Can't create repeat with index < 1");
      }
      return Z3_mk_repeat(c, narrow_index(op, op.indices[0]), a);
    case Rotate_Left:
      return Z3_mk_rotate_left(c, narrow_index(op, op.indices[0]), a);
    case Rotate_Right:
      return Z3_mk_rotate_right(c, narrow_index(op, op.indices[0]), a);
    case BV_To_Nat:
    case UBV_To_Int: return Z3_mk_bv2int(c, a, /* is_signed */ false);
    case SBV_To_Int: return Z3_mk_bv2int(c, a, /* is_signed */ true);
    case Int_To_BV: return Z3_mk_int2bv(c, narrow_index(op, op.indices[0]), a);
    case Divisible:
      if (op.indices[0] < 1)
      {
        throw IncorrectUsageException("Can't create divisible with index < 1");
      }
      // Z3 keeps the divisor as an int parameter
      return Z3_mk_divides(
          c,
          Z3_mk_int(c,
                    detail::narrow<int>(op.indices[0], "a divisible index"),
                    Z3_mk_int_sort(c)),
          a);
    default: throw_unsupported(op.prim_op, 1);
  }
}

/** The term of po applied to two arguments
 *  @throws as throw_unsupported where this backend has no such op
 */
static Z3_ast binary_term(Z3_context c, PrimOp po, Z3_ast a, Z3_ast b)
{
  const std::array<Z3_ast, 2> args{ { a, b } };
  switch (po)
  {
    case And: return Z3_mk_and(c, 2, args.data());
    case Or: return Z3_mk_or(c, 2, args.data());
    case Xor: return Z3_mk_xor(c, a, b);
    case Implies: return Z3_mk_implies(c, a, b);
    case Equal: return Z3_mk_eq(c, a, b);
    case Distinct: return Z3_mk_distinct(c, 2, args.data());
    case Plus: return Z3_mk_add(c, 2, args.data());
    case Minus: return Z3_mk_sub(c, 2, args.data());
    case Mult: return Z3_mk_mul(c, 2, args.data());
    case Div: return ext_Z3_mk_real_div(c, a, b);
    case Lt: return Z3_mk_lt(c, a, b);
    case Le: return Z3_mk_le(c, a, b);
    case Gt: return Z3_mk_gt(c, a, b);
    case Ge: return Z3_mk_ge(c, a, b);
    case Mod: return Z3_mk_mod(c, a, b);
    case Pow: return Z3_mk_power(c, a, b);
    case IntDiv: return Z3_mk_div(c, a, b);
    case Concat: return Z3_mk_concat(c, a, b);
    case BVAnd: return Z3_mk_bvand(c, a, b);
    case BVOr: return Z3_mk_bvor(c, a, b);
    case BVXor: return Z3_mk_bvxor(c, a, b);
    case BVNand: return Z3_mk_bvnand(c, a, b);
    case BVNor: return Z3_mk_bvnor(c, a, b);
    case BVXnor: return Z3_mk_bvxnor(c, a, b);
    case BVAdd: return Z3_mk_bvadd(c, a, b);
    case BVSub: return Z3_mk_bvsub(c, a, b);
    case BVMul: return Z3_mk_bvmul(c, a, b);
    case BVUdiv: return Z3_mk_bvudiv(c, a, b);
    case BVSdiv: return Z3_mk_bvsdiv(c, a, b);
    case BVUrem: return Z3_mk_bvurem(c, a, b);
    case BVSrem: return Z3_mk_bvsrem(c, a, b);
    case BVSmod: return Z3_mk_bvsmod(c, a, b);
    case BVShl: return Z3_mk_bvshl(c, a, b);
    case BVAshr: return Z3_mk_bvashr(c, a, b);
    case BVLshr: return Z3_mk_bvlshr(c, a, b);
    case BVComp: return ext_Z3_mk_bvcomp(c, a, b);
    case BVUlt: return Z3_mk_bvult(c, a, b);
    case BVUle: return Z3_mk_bvule(c, a, b);
    case BVUgt: return Z3_mk_bvugt(c, a, b);
    case BVUge: return Z3_mk_bvuge(c, a, b);
    case BVSlt: return Z3_mk_bvslt(c, a, b);
    case BVSle: return Z3_mk_bvsle(c, a, b);
    case BVSgt: return Z3_mk_bvsgt(c, a, b);
    case BVSge: return Z3_mk_bvsge(c, a, b);
    case Select: return Z3_mk_select(c, a, b);
    default: throw_unsupported(po, 2);
  }
}

/** The term of op applied to terms, three or more, whose Z3 terms are args,
 *  in a single Z3 call where Z3 has one and through make_nary_term otherwise
 */
static Term variadic_term(const AbsSmtSolver * solver,
                          const std::shared_ptr<z3::context> & ctx,
                          const Op & op,
                          const TermVec & terms,
                          const vector<Z3_ast> & args)
{
  const unsigned n = narrow_num_args(args.size());
  Z3_ast res;
  switch (op.prim_op)
  {
    case And: res = Z3_mk_and(*ctx, n, args.data()); break;
    case Or: res = Z3_mk_or(*ctx, n, args.data()); break;
    case Distinct: res = Z3_mk_distinct(*ctx, n, args.data()); break;
    case Plus: res = Z3_mk_add(*ctx, n, args.data()); break;
    case Minus: res = Z3_mk_sub(*ctx, n, args.data()); break;
    case Mult: res = Z3_mk_mul(*ctx, n, args.data()); break;
    default: return make_nary_term(solver, op, terms);
  }
  return std::make_shared<Z3Term>(ctx, to_expr(*ctx, res));
}

/* Z3Solver implementation */

struct Z3Solver::Instance
{
  Instance(const std::shared_ptr<z3::context> & c,
           const z3::solver & s,
           const std::string & l = "ALL")
      : ctx(c), slv(s), logic(l)
  {
  }

  // slv lives in ctx, so ctx is declared first and outlives it
  std::shared_ptr<z3::context> ctx;
  z3::solver slv;
  // the logic slv was made for, ALL for Z3's default, which SMT-LIB needs
  // named before any declaration
  std::string logic;
};

Z3Solver::Z3Solver()
    : AbsSmtSolver(Z3),
      ctx(std::make_shared<z3::context>()),
      solver_params(*ctx)
{
}

void Z3Solver::set_opt(const std::string option, const std::string value)
{
  const char * o = option.c_str();
  const char * v = value.c_str();

  // READ PLEASE
  // The easiest handling of Z3's set function's param requirements is to have
  // vectors with the names of different options in the list corresponding with
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
      solver_params.set("model", true);
    }
    else if (value == "false")
    {
      solver_params.set("model", false);
    }
    else
    {
      throw IncorrectUsageException(
          "produce-models takes values true or false");
    }
  }
  else if (option == "time-limit")
  {
    unsigned milliseconds = std::stod(value) * 1000;
    solver_params.set("timeout", milliseconds);
  }
  else if (option == "produce-unsat-assumptions")
  {
    if (value == "true")
    {
      solver_params.set("unsat_core", true);
    }
    else if (value == "false")
    {
      solver_params.set("unsat_core", false);
    }
    else
    {
      throw IncorrectUsageException(
          "produce-unsat-assumptions takes values true or false");
    }
  }
  else if (bool_opts.find(option) != bool_opts.end())
  {
    if (value == "true")
    {
      solver_params.set(o, true);
    }
    else if (value == "false")
    {
      solver_params.set(o, false);
    }
    else
    {
      throw IncorrectUsageException("Expected a boolean value.");
    }
  }
  else if (string_opts.find(option) != string_opts.end())
  {
    solver_params.set(o, v);
  }
  else if (int_opts.find(option) != int_opts.end())
  {
    try
    {
      double num = stoi(value, nullptr, 10);
      solver_params.set(o, num);
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
  if (instance)
  {
    instance->slv.set(solver_params);
  }
}

void Z3Solver::set_logic(const std::string logic)
{
  if (instance)
  {
    throw IncorrectUsageException(
        "Z3 can only set the logic once, before the first assertion, check "
        "or push");
  }
  try
  {
    instance =
        std::make_shared<Instance>(ctx, z3::solver(*ctx, logic.c_str()), logic);
  }
  catch (z3::exception & e)
  {
    throw IncorrectUsageException(e.msg());
  }
  instance->slv.set(solver_params);
}

Term Z3Solver::make_term(bool b) const
{
  z3::expr z_term = ctx->bool_val(false);
  if (b)
  {
    z_term = ctx->bool_val(true);
  }

  return std::make_shared<Z3Term>(ctx, z_term);
}
void Z3Solver::add_constructor(z3::sort dtsort,
                               z3::constructors * cs,
                               const DatatypeConstructorDecl & cons) const
{
  auto z3cons = std::static_pointer_cast<Z3DatatypeConstructorDecl>(cons);
  auto & cname = z3cons->constructorname;
  auto recognizer = "is-"s + cname;
  // the decl keeps its self placeholders, so another datatype it is added to
  // gets its own sort for them
  std::vector<z3::symbol> fieldnames;
  std::vector<z3::sort> sorts;
  for (const auto & [name, sort] : z3cons->selectors)
  {
    fieldnames.push_back(ctx->str_symbol(name.c_str()));
    sorts.push_back(static_cast<Z3_sort>(sort) == nullptr ? dtsort : sort);
  }
  cs->add(ctx->str_symbol(cname.c_str()),
          ctx->str_symbol(recognizer.c_str()),
          detail::narrow<unsigned>(fieldnames.size(), "a number of fields"),
          fieldnames.data(),
          sorts.data());
}

Sort Z3Solver::make_sort(const DatatypeDecl & d) const
{
  try
  {
    std::shared_ptr<Z3DatatypeDecl> cd =
        backend_pointer_cast<Z3DatatypeDecl>(d);
    // as SMT-LIB declares a datatype once
    if (cd->used)
    {
      throw IncorrectUsageException("Datatype declaration " + cd->name
                                    + " was used for a sort already");
    }
    auto dtsort = ctx->datatype_sort(ctx->str_symbol(cd->name.c_str()));
    z3::constructors cs{ *ctx };
    for (auto cons : cd->consvec)
    {
      add_constructor(dtsort, &cs, cons);
    }
    auto sort = ctx->datatype(ctx->str_symbol(cd->name.data()), cs);
    cd->used = true;
    return std::make_shared<Z3Sort>(ctx, sort);
  }
  catch (z3::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

SortVec Z3Solver::make_datatype_sorts(
    const std::vector<DatatypeDecl> & decls) const
{
  std::vector<z3::symbol> syms;
  std::vector<std::unique_ptr<z3::constructors>> consvec;
  std::vector<z3::constructor_list> clvec{};
  std::vector<z3::constructor_list *> clpvec{};  // constructor_list pointer vec
  // clpvec points into clvec, so clvec must not reallocate
  clvec.reserve(decls.size());
  std::vector<std::shared_ptr<Z3DatatypeDecl>> z3_decls;
  for (auto & absdecl : decls)
  {
    std::shared_ptr<Z3DatatypeDecl> decl =
        backend_pointer_cast<Z3DatatypeDecl>(absdecl);
    // as SMT-LIB declares a datatype once
    if (decl->used)
    {
      throw IncorrectUsageException("Datatype declaration " + decl->name
                                    + " was used for a sort already");
    }
    z3_decls.push_back(decl);
    auto dt_symbol = ctx->str_symbol(decl->name.c_str());
    auto dt_sort = ctx->datatype_sort(dt_symbol);
    syms.push_back(dt_symbol);
    auto cs = std::make_unique<z3::constructors>(*ctx);
    for (auto cons : decl->consvec) add_constructor(dt_sort, cs.get(), cons);
    clvec.emplace_back(*cs);
    clpvec.push_back(&clvec.back());
    consvec.push_back(std::move(cs));
  }
  auto raw_sorts = ctx->datatypes(
      detail::narrow<unsigned>(decls.size(), "a number of datatypes"),
      syms.data(),
      clpvec.data());
  for (const auto & decl : z3_decls)
  {
    decl->used = true;
  }
  SortVec sorts{};
  for (auto s : raw_sorts) sorts.push_back(std::make_shared<Z3Sort>(ctx, s));
  return sorts;
}

DatatypeDecl Z3Solver::make_datatype_decl(const std::string & s) const
{
  try
  {
    return std::make_shared<Z3DatatypeDecl>(s);
  }
  catch (z3::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

DatatypeConstructorDecl Z3Solver::make_datatype_constructor_decl(
    const std::string s) const
{
  try
  {
    return std::make_shared<Z3DatatypeConstructorDecl>(ctx, s);
  }
  catch (z3::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Z3Solver::add_constructor(DatatypeDecl & dt,
                               const DatatypeConstructorDecl & cons) const
{
  try
  {
    auto z3dt = backend_pointer_cast<Z3DatatypeDecl>(dt);
    z3dt->consvec.push_back(
        backend_pointer_cast<Z3DatatypeConstructorDecl>(cons));
  }
  catch (z3::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Z3Solver::add_selector(DatatypeConstructorDecl & dt,
                            const std::string & name,
                            const Sort & s) const
{
  try
  {
    auto cdt = backend_pointer_cast<Z3DatatypeConstructorDecl>(dt);
    cdt->selectors.emplace_back(name, get_z3_sort(s)->get_z3_type());
  }
  catch (z3::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Z3Solver::add_selector_self(DatatypeConstructorDecl & dt,
                                 const std::string & name) const
{
  try
  {
    auto cdt = backend_pointer_cast<Z3DatatypeConstructorDecl>(dt);
    cdt->selectors.emplace_back(name, z3::sort(*ctx));
  }
  catch (z3::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Z3Solver::get_constructor(const Sort & s, std::string name) const
{
  try
  {
    auto z3sort = get_z3_sort(s);
    z3::sort dt = z3sort->get_z3_datatype();
    for (auto cons_raw : dt.constructors())
    {
      z3::func_decl cons{ *ctx, cons_raw };
      if (cons.name().str() == name) return std::make_shared<Z3Term>(ctx, cons);
    }
    throw IncorrectUsageException("Constructor " + name + " not found");
  }
  catch (z3::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Z3Solver::get_tester(const Sort & s, std::string name) const
{
  auto z3sort = get_z3_sort(s);
  z3::sort dt = z3sort->get_z3_datatype();
  unsigned num_constructors = Z3_get_datatype_sort_num_constructors(*ctx, dt);
  for (unsigned i = 0; i < num_constructors; i++)
  {
    z3::func_decl cons{ *ctx, Z3_get_datatype_sort_constructor(*ctx, dt, i) };
    if (cons.name().str() == name)
      return std::make_shared<Z3Term>(
          ctx,
          z3::func_decl{ *ctx, Z3_get_datatype_sort_recognizer(*ctx, dt, i) });
  }
  throw IncorrectUsageException("Tester " + name + " not found");
}

Term Z3Solver::get_selector(const Sort & s,
                            std::string con,
                            std::string name) const
{
  auto cons = get_constructor(s, con);
  auto func = backend_pointer_cast<Z3Term>(cons)->get_z3_func_decl();
  for (auto field : func.accessors())
  {
    if (field.name().str() == name) return std::make_shared<Z3Term>(ctx, field);
  }
  throw IncorrectUsageException("Selector " + name + " not found");
}

Term Z3Solver::make_term(int64_t i, const Sort & sort) const
{
  SortKind sk = sort->get_sort_kind();
  z3::expr z_term = z3::expr(*ctx);
  if (sk == INT)
  {
    z_term = ctx->int_val(i);
  }
  else if (sk == REAL)
  {
    z_term = ctx->real_val(i);
  }
  else if (sk == BV)
  {
    z_term = ctx->bv_val(i, narrow_width(sort->get_width()));
  }
  else
  {
    string msg("Can't create value ");
    msg += std::to_string(i);
    msg += " with sort ";
    msg += sort->to_string();
    throw IncorrectUsageException(msg);
  }

  return std::make_shared<Z3Term>(ctx, z_term);
}

Term Z3Solver::make_term(const std::string val,
                         const Sort & sort,
                         uint64_t base) const
{
  z3::expr z_term = z3::expr(*ctx);
  SortKind sk = sort->get_sort_kind();

  if (sk == BV)
  {
    std::uint64_t width = sort->get_width();
    if (width <= 64)
    {
      z_term = ctx->bv_val(detail::bv_value_to_uint64(val, base, width),
                           narrow_width(width));
    }
    else
    {
      std::vector<std::uint32_t> words =
          detail::bv_value_to_words(val, base, width);
      // Z3 reads bits[0] as the lowest bit
      std::unique_ptr<bool[]> bits = std::make_unique<bool[]>(width);
      for (std::uint64_t i = 0; i < width; ++i)
      {
        bits[i] = (words[i / 32] >> (i % 32)) & 1;
      }
      z_term = ctx->bv_val(narrow_width(width), bits.get());
    }
  }
  else if (sk == REAL || sk == INT)
  {
    std::string decimal = arith_value_to_decimal(sk, val, base);
    // Z3 reads "" and "-" as 0, and "1.2.3" as some Real
    std::string msg =
        "Can't create value " + val + " with sort " + sort->to_string();
    if (!is_arith_number(sk, decimal))
    {
      throw IncorrectUsageException(msg);
    }
    try
    {
      z_term = sk == REAL ? ctx->real_val(decimal.c_str())
                          : ctx->int_val(decimal.c_str());
    }
    catch (z3::exception & e)
    {
      // such as division by zero
      throw IncorrectUsageException(msg + ": " + e.msg());
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

  return std::make_shared<Z3Term>(ctx, z_term);
}

Term Z3Solver::make_term(const Term & val, const Sort & sort) const
{
  std::shared_ptr<Z3Term> zterm = get_z3_term(val);
  std::shared_ptr<Z3Sort> zsort = get_z3_sort(sort);

  if (zsort->is_function || zterm->is_function)
  {
    throw IncorrectUsageException(
        "Cannot create constant array with function element");
  }
  z3::sort arrtype = zsort->type;
  if (!arrtype.is_array())
  {
    throw IncorrectUsageException("Can't make a constant array of sort "
                                  + sort->to_string()
                                  + ", which is not an array sort");
  }

  Z3_ast c_array = Z3_mk_const_array(*ctx, arrtype.array_domain(), zterm->term);
  z3::expr final = to_expr(*ctx, c_array);
  return std::make_shared<Z3Term>(ctx, final);
}

void Z3Solver::assert_formula(const Term & t)
{
  std::shared_ptr<Z3Term> zterm = get_z3_term(t);
  if (zterm->is_function)
  {
    throw IncorrectUsageException(
        "Attempted to assert a function directly to solver");
  }
  get_z3_solver()->add(zterm->term);
}

Result Z3Solver::check_sat()
{
  last_query_assuming = false;
  z3::check_result r = get_z3_solver()->check();
  if (r == z3::unsat)
  {
    return Result(UNSAT);
  }
  else if (r == z3::sat)
  {
    return Result(SAT);
  }
  else if (r == z3::unknown)
  {
    return Result(UNKNOWN, instance->slv.reason_unknown());
  }
  else
  {
    throw NotImplementedException("Unimplemented result type from Z3");
  }
}

Result Z3Solver::do_check_sat_assuming(const TermVec & assumptions)
{
  z3::expr_vector z3assumps(*ctx);

  for (auto a : assumptions)
  {
    z3assumps.push_back(get_z3_term(a)->term);
  }

  last_query_assuming = true;
  z3::check_result r = get_z3_solver()->check(z3assumps);
  if (r == z3::unsat)
  {
    return Result(UNSAT);
  }
  else if (r == z3::sat)
  {
    return Result(SAT);
  }
  else if (r == z3::unknown)
  {
    return Result(UNKNOWN, instance->slv.reason_unknown());
  }
  else
  {
    throw NotImplementedException("Unimplemented result type from Z3");
  }
}

void Z3Solver::do_push(uint64_t num)
{
  for (uint64_t i = 0; i < num; i++)
  {
    get_z3_solver()->push();
  }
}

void Z3Solver::do_pop(uint64_t num)
{
  get_z3_solver()->pop(narrow_levels(num));
}

Term Z3Solver::get_value(const Term & t) const
{
  shared_ptr<Z3Term> zterm = get_z3_term(t);
  if (zterm->is_function)
  {
    throw IncorrectUsageException("Cannot evaluate a function.");
  }
  if (!instance)
  {
    throw IncorrectUsageException(
        "Last call to check_sat was not sat, cannot get a model.");
  }
  z3::model model = instance->slv.get_model();
  z3::expr eval = model.eval(zterm->term, true);
  return std::make_shared<Z3Term>(ctx, eval);
}

UnorderedTermMap Z3Solver::get_array_values(const Term & arr,
                                            Term & out_const_base) const
{
  out_const_base = nullptr;
  shared_ptr<Z3Term> zarr = get_z3_term(arr);
  if (!instance)
  {
    throw IncorrectUsageException(
        "Last call to check_sat was not sat, cannot get a model.");
  }
  z3::model model = instance->slv.get_model();
  // Z3 gives an array model as a chain of stores over a constant base,
  // outermost store first.
  z3::expr zval = model.eval(zarr->term, true);

  std::vector<std::pair<Term, Term>> stores;
  while (zval.is_app() && zval.decl().decl_kind() == Z3_OP_STORE)
  {
    stores.push_back({ std::make_shared<Z3Term>(ctx, zval.arg(1)),
                       std::make_shared<Z3Term>(ctx, zval.arg(2)) });
    zval = zval.arg(0);
  }

  if (zval.is_app() && zval.decl().decl_kind() == Z3_OP_CONST_ARRAY)
  {
    out_const_base = std::make_shared<Z3Term>(ctx, zval.arg(0));
  }
  else
  {
    // Nothing else is expected under the stores. Say which head turned up
    // rather than return a map that quietly omits it.
    throw NotImplementedException("Z3 gave an array model headed by "
                                  + zval.to_string()
                                  + ", which has no constant base");
  }

  return store_chain_values(stores);
}

void Z3Solver::get_unsat_assumptions(UnorderedTermSet & out) const
{
  // in smt-switch, should throw exception if last query
  // was check_sat instead of check_sat_assuming
  if (!last_query_assuming || !instance)
  {
    throw SmtException(
        "Can only call get_unsat_assumptions after check_sat_assuming");
  }
  z3::expr_vector core = instance->slv.unsat_core();
  for (const auto & c : core)
  {
    out.insert(std::make_shared<Z3Term>(ctx, c));
  }
}

Sort Z3Solver::make_sort(const std::string name, uint64_t arity) const
{
  if (!arity)
  {
    const char * c = name.c_str();
    z3::symbol func_name = ctx->str_symbol(c);
    z3::sort z_sort = ctx->uninterpreted_sort(func_name);
    return std::make_shared<Z3Sort>(ctx, z_sort);
  }
  else
  {
    throw NotImplementedException(
        "Z3 does not support uninterpreted type with non-zero arity.");
  }
}

Sort Z3Solver::make_sort(SortKind sk) const
{
  z3::sort z_sort = z3::sort(*ctx);

  if (sk == BOOL)
  {
    z_sort = ctx->bool_sort();
  }
  else if (sk == INT)
  {
    z_sort = ctx->int_sort();
  }
  else if (sk == REAL)
  {
    z_sort = ctx->real_sort();
  }
  else
  {
    std::string msg("Can't create sort with sort constructor ");
    msg += to_string(sk);
    msg += " and no arguments";
    throw IncorrectUsageException(msg.c_str());
  }

  Sort final_sort = std::make_shared<Z3Sort>(ctx, z_sort);
  return final_sort;
}

Sort Z3Solver::make_sort(SortKind sk, uint64_t size) const
{
  if (sk == BV)
  {
    return std::make_shared<Z3Sort>(ctx, ctx->bv_sort(narrow_width(size)));
  }
  else
  {
    std::string msg("Can't create sort with sort constructor ");
    msg += to_string(sk);
    msg += " and an integer argument";
    throw IncorrectUsageException(msg.c_str());
  }
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
    unsigned arity = narrow_num_args(sorts.size() - 1);

    std::vector<z3::sort> zsorts;
    zsorts.reserve(arity);
    z3::sort z_sort = z3::sort(*ctx);

    for (unsigned i = 0; i < arity; i++)
    {
      z_sort = get_z3_sort(sorts[i])->type;
      zsorts.push_back(z_sort);
    }

    Sort sort = sorts.back();
    z_sort = get_z3_sort(sort)->type;

    const char * c = "throwaway name";
    z3::symbol func_name = ctx->str_symbol(c);
    z3::func_decl z_func =
        ctx->function(func_name, arity, zsorts.data(), z_sort);

    return std::make_shared<Z3Sort>(ctx, z_func);
  }
  else if (sk == ARRAY && sorts.size() == 2)
  {
    std::shared_ptr<Z3Sort> cidxsort = get_z3_sort(sorts[0]);
    std::shared_ptr<Z3Sort> celemsort = get_z3_sort(sorts[1]);
    return std::make_shared<Z3Sort>(
        ctx, ctx->array_sort(cidxsort->type, celemsort->type));
  }
  else
  {
    std::string msg("Can't create sort from sort constructor ");
    msg += to_string(sk);
    msg += " with a vector of sorts of size " + std::to_string(sorts.size());
    throw IncorrectUsageException(msg.c_str());
  }
}

Term Z3Solver::make_symbol(const std::string name, const Sort & sort)
{
  if (symbol_table.find(name) != symbol_table.end())
  {
    throw IncorrectUsageException("symbol " + name + " has already been used.");
  }

  shared_ptr<Z3Sort> zsort = get_z3_sort(sort);
  const char * c = name.c_str();
  z3::symbol z_name = ctx->str_symbol(c);

  Term sym;
  if (zsort->get_sort_kind() == FUNCTION)
  {
    // nb this is creating a func_decl
    z3::func_decl sort_func = zsort->z_func;

    z3::sort_vector domain(*ctx);
    for (unsigned i = 0; i < sort_func.arity(); i++)
    {
      domain.push_back(sort_func.domain(i));
    }

    z3::func_decl z_func = ctx->function(c, domain, sort_func.range());
    sym = std::make_shared<Z3Term>(ctx, z_func);
  }
  else
  {
    // nb this is creating an expr
    z3::expr z_term = ctx->constant(z_name, zsort->type);

    sym = std::make_shared<Z3Term>(ctx, z_term);
  }
  symbol_table[name] = sym;
  return sym;
}

Term Z3Solver::get_symbol(const std::string & name) const
{
  auto it = symbol_table.find(name);
  if (it == symbol_table.end())
  {
    throw IncorrectUsageException("Symbol named " + name + " does not exist.");
  }
  return it->second;
}

Term Z3Solver::make_param(const std::string name, const Sort & sort) const
{
  shared_ptr<Z3Sort> zsort = get_z3_sort(sort);

  if (zsort->is_function)
  {
    throw IncorrectUsageException("Functions cannot be parameters");
  }

  // Z3 gives a constant of the same name and sort back as the same term,
  // so a constant named `name` would be a symbol of that name, and a
  // quantifier over it would bind the symbol. A fresh one never is.
  z3::expr z_term(*ctx, Z3_mk_fresh_const(*ctx, name.c_str(), zsort->type));
  // mark as a parameter by passing true
  return std::make_shared<Z3Term>(ctx, z_term, true);
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
  else if (op.prim_op == Forall || op.prim_op == Exists)
  {
    check_quantifier_binders(op, terms);
  }

  if (size == 1)
  {
    shared_ptr<Z3Term> zterm = get_z3_term(terms[0]);

    if (zterm->is_function)
    {
      if (op.prim_op != Apply_Constructor)
      {
        throw IncorrectUsageException(
            "Cannot make a unary operator term with a function.");
      }
      res = Z3_mk_app(*ctx, zterm->get_z3_func_decl(), 0, 0);
    }
    else
    {
      res = unary_term(*ctx, op, zterm->term);
    }

    return std::make_shared<Z3Term>(ctx, to_expr(*ctx, res));
  }

  // Z3 represents datatype constructors, testers and selectors as functions,
  // so applying one is an Apply
  if ((op == Apply_Constructor || op == Apply_Tester || op == Apply_Selector)
      && get_z3_term(terms[0])->is_function)
  {
    op = Op(Apply);
  }

  // the operands, leaving out the function an Apply applies
  vector<Z3_ast> zargs;
  zargs.reserve(size);
  for (size_t i = op.prim_op == Apply ? 1 : 0; i < size; ++i)
  {
    shared_ptr<Z3Term> zterm = get_z3_term(terms[i]);
    if (zterm->is_function)
    {
      throw IncorrectUsageException("Cannot use a function as an argument to "
                                    + op.to_string());
    }
    zargs.push_back(zterm->term);
  }

  if (op.prim_op == Apply)
  {
    shared_ptr<Z3Term> zfun = get_z3_term(terms[0]);
    if (!zfun->is_function)
    {
      string msg(
          "Expecting an uninterpreted function to be used with Apply but got ");
      msg += terms[0]->to_string();
      throw IncorrectUsageException(msg);
    }
    res =
        Z3_mk_app(*ctx, zfun->z_func, narrow_num_args(size - 1), zargs.data());
  }
  else if (op.prim_op == Forall || op.prim_op == Exists)
  {
    // the last term is the body, bound by the rest
    z3::expr_vector params(*ctx);
    for (size_t i = 0; i + 1 < size; ++i)
    {
      params.push_back(to_expr(*ctx, zargs[i]));
    }
    z3::expr body = to_expr(*ctx, zargs.back());
    res = op.prim_op == Forall ? forall(params, body) : exists(params, body);
  }
  else if (size == 2)
  {
    res = binary_term(*ctx, op.prim_op, zargs[0], zargs[1]);
  }
  else if (size == 3 && op.prim_op == Ite)
  {
    res = Z3_mk_ite(*ctx, zargs[0], zargs[1], zargs[2]);
  }
  else if (size == 3 && op.prim_op == Store)
  {
    res = Z3_mk_store(*ctx, zargs[0], zargs[1], zargs[2]);
  }
  else
  {
    return variadic_term(this, ctx, op, terms, zargs);
  }

  return std::make_shared<Z3Term>(ctx, to_expr(*ctx, res));
}

void Z3Solver::do_reset()
{
  instance.reset();
  symbol_table.clear();
  solver_params = z3::params(*ctx);
}

void Z3Solver::do_reset_assertions()
{
  // the logic stays, as SMT-LIB's reset-assertions keeps it
  if (instance)
  {
    instance->slv.reset();
  }
}

Term Z3Solver::substitute(const Term term,
                          const UnorderedTermMap & substitution_map) const
{
  // z3 expression vectors that represent the
  // substitution map, i.e.:
  // substitutionmap[z3sources[i]] = z3destinations[i]
  z3::expr_vector z3sources(*ctx);
  z3::expr_vector z3destinations(*ctx);

  // z3 counterpart of `term`
  shared_ptr<Z3Term> z3term = get_z3_term(term);
  z3::expr z3expr = to_expr(*ctx, z3term->term);
  // populate the z3 expr_vectors according to the substitution map
  for (auto p : substitution_map)
  {
    Term from_term = p.first;
    Term to_term = p.second;
    shared_ptr<Z3Term> z3_from_term = get_z3_term(from_term);
    shared_ptr<Z3Term> z3_to_term = get_z3_term(to_term);
    z3sources.push_back(z3_from_term->term);
    z3destinations.push_back(z3_to_term->term);
  }

  // perform the substitution and return the result
  z3::expr result = z3expr.substitute(z3sources, z3destinations);
  return std::make_shared<Z3Term>(ctx, result);
}

void Z3Solver::dump_smt2(std::string filename) const
{
  // with no Z3 solver yet nothing is asserted, and making one here would
  // fix the logic
  z3::expr_vector assertions =
      instance ? instance->slv.assertions() : z3::expr_vector(*ctx);
  // Z3 prints the assumptions and then the formula as assertions
  z3::expr formula = ctx->bool_val(true);
  std::vector<Z3_ast> assumptions;
  if (!assertions.empty())
  {
    formula = assertions.back();
    for (unsigned i = 0; i + 1 < assertions.size(); ++i)
    {
      assumptions.push_back(assertions[i]);
    }
  }
  std::ofstream out(filename);
  out << Z3_benchmark_to_smtlib_string(
      *ctx,
      /* name */ "",
      instance ? instance->logic.c_str() : "ALL",
      /* status */ "unknown",
      /* attributes */ "",
      static_cast<unsigned>(assumptions.size()),
      assumptions.data(),
      formula);
}

std::shared_ptr<z3::context> Z3Solver::get_z3_context() { return ctx; }

std::shared_ptr<z3::solver> Z3Solver::get_z3_solver()
{
  if (!instance)
  {
    instance = std::make_shared<Instance>(ctx, z3::solver(*ctx));
    instance->slv.set(solver_params);
  }
  return std::shared_ptr<z3::solver>(instance, &instance->slv);
}

std::shared_ptr<Z3Sort> Z3Solver::get_z3_sort(const Sort & s) const
{
  std::shared_ptr<Z3Sort> zs = backend_pointer_cast<Z3Sort>(s);
  if (zs->ctx != ctx)
  {
    detail::throw_foreign_handle(s);
  }
  return zs;
}

std::shared_ptr<Z3Term> Z3Solver::get_z3_term(const Term & t) const
{
  std::shared_ptr<Z3Term> zt = backend_pointer_cast<Z3Term>(t);
  if (zt->ctx != ctx)
  {
    detail::throw_foreign_handle(t);
  }
  return zt;
}

/* end Z3Solver implementation */

}  // namespace smt
