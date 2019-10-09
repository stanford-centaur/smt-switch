#include "msat_solver.h"
#include "msat_extensions.h"
#include "msat_sort.h"
#include "msat_term.h"

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
    // { Const_Array, }
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
      { Lt, ext_msat_make_lt },
      { Le, msat_make_leq },
      { Gt, ext_msat_make_gt },
      { Ge, ext_msat_make_geq },
      // TODO: Actually implement mod and pow
      { Mod, ext_msat_make_mod },
      { Pow, ext_msat_make_pow },
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
      { Select, msat_make_array_read } });

const unordered_map<PrimOp, msat_tern_fun> msat_ternary_ops(
    { { Ite, msat_make_term_ite }, { Store, msat_make_array_write } });

// other special cases:
// Apply -- needs to handle arbitrarily many terms

// MsatSolver implementation

void MsatSolver::set_opt(const string option, bool value) const
{
  msat_set_option(cfg, option.c_str(), value ? "true" : "false");
}

void MsatSolver::set_opt(const string option, const string value) const
{
  msat_set_option(cfg, option.c_str(), value.c_str());
}

void MsatSolver::set_logic(const std::string logic) const
{
  // TODO: See if there's a correct way to do this
  // this seems like a no-op (doesn't complain for other sorts)
  msat_set_option(cfg, "logic", logic.c_str());
}

void MsatSolver::assert_formula(const Term & t) const
{
  shared_ptr<MsatTerm> mterm = static_pointer_cast<MsatTerm>(t);

  if (!msat_assert_formula(env, mterm->term))
  {
    string msg("Cannot assert term: ");
    msg += msat_to_smtlib2_term(env, mterm->term);
    throw IncorrectUsageException(msg);
  }
}

Result MsatSolver::check_sat() const
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

Result MsatSolver::check_sat_assuming(const TermVec & assumptions) const
{
  vector<msat_term> msat_assumptions;
  shared_ptr<MsatTerm> ma;
  for (auto a : assumptions)
  {
    ma = static_pointer_cast<MsatTerm>(a);
    msat_assumptions.push_back(ma->term);
  }

  msat_result mres = msat_solve_with_assumptions(
      env, &msat_assumptions[0], msat_assumptions.size());

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

void MsatSolver::push(unsigned int num) const
{
  for (unsigned int i = 0; i < num; i++)
  {
    msat_push_backtrack_point(env);
  }
}

void MsatSolver::pop(unsigned int num) const
{
  for (unsigned int i = 0; i < num; i++)
  {
    msat_pop_backtrack_point(env);
  }
}

Term MsatSolver::get_value(Term & t) const
{
  shared_ptr<MsatTerm> mterm = static_pointer_cast<MsatTerm>(t);
  msat_term val = msat_get_model_value(env, mterm->term);

  if (MSAT_ERROR_TERM(val))
  {
    string msg("Error getting value for ");
    msg += msat_to_smtlib2_term(env, mterm->term);
    msg +=
        ".\nBe sure the last check-sat call was sat and the term only contains "
        "constants in this solving environment.";
    throw IncorrectUsageException(msg);
  }

  return Term(new MsatTerm(env, val));
}

Sort MsatSolver::make_sort(const std::string name, unsigned int arity) const
{
  if (!arity)
  {
    return Sort(new MsatSort(env, msat_get_simple_type(env, name.c_str())));
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
    Sort s(new MsatSort(env, msat_get_bool_type(env)));
    return s;
  }
  else if (sk == INT)
  {
    Sort s(new MsatSort(env, msat_get_integer_type(env)));
    return s;
  }
  else if (sk == REAL)
  {
    Sort s(new MsatSort(env, msat_get_rational_type(env)));
    return s;
  }
  else
  {
    std::string msg("Can't create sort with sort constructor ");
    msg += to_string(sk);
    msg += " and no arguments";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort MsatSolver::make_sort(SortKind sk, unsigned int size) const
{
  if (sk == BV)
  {
    Sort s(new MsatSort(env, msat_get_bv_type(env, size)));
    return s;
  }
  else
  {
    std::string msg("Can't create sort with sort constructor ");
    msg += to_string(sk);
    msg += " and an integer argument";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort MsatSolver::make_sort(SortKind sk,
                           const Sort & idxsort,
                           const Sort & elemsort) const
{
  if (sk == ARRAY)
  {
    std::shared_ptr<MsatSort> msort0 =
        std::static_pointer_cast<MsatSort>(idxsort);
    std::shared_ptr<MsatSort> msort1 =
        std::static_pointer_cast<MsatSort>(elemsort);
    Sort s(new MsatSort(env,
                        msat_get_array_type(env, msort0->type, msort1->type)));
    return s;
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
                           const std::vector<Sort> & sorts,
                           const Sort & sort) const
{
  if (sorts.size() == 0)
  {
    return make_sort(sort->get_sort_kind());
  }
  else if (sk != FUNCTION)
  {
    throw IncorrectUsageException("Expecting function sort kind when creating sort with a vector of domain sorts");
  }

  string decl_name("internal_ref_fun");

  std::vector<msat_type> msorts;
  msorts.reserve(sorts.size());
  msat_type msort;
  for (Sort s : sorts)
  {
    msort = std::static_pointer_cast<MsatSort>(s)->type;
    msorts.push_back(msort);
    decl_name += ("_" + s->to_string());
  }
  msort = std::static_pointer_cast<MsatSort>(sort)->type;
  decl_name += ("_return_" + sort->to_string());
  msat_type mfunsort =
      msat_get_function_type(env, &msorts[0], msorts.size(), msort);

  // creating a reference decl, because it's the only way to get codomain and domain sorts
  // i.e. there's no msat_is_function_type(msat_env, msat_type)
  msat_decl ref_fun_decl = msat_declare_function(env, decl_name.c_str(), mfunsort);

  Sort funsort(new MsatSort(env, mfunsort, ref_fun_decl));
  return funsort;
}

Term MsatSolver::make_value(bool b) const
{
  if (b)
  {
    return Term(new MsatTerm(env, msat_make_true(env)));
  }
  else
  {
    return Term(new MsatTerm(env, msat_make_false(env)));
  }
}

Term MsatSolver::make_value(unsigned int i, const Sort & sort) const
{
  SortKind sk = sort->get_sort_kind();
  if (sk == BV)
  {
    return Term(
        new MsatTerm(env, msat_make_bv_int_number(env, i, sort->get_width())));
  }
  else if (sk == REAL || sk == INT)
  {
    return Term(new MsatTerm(env, msat_make_int_number(env, i)));
  }
  else
  {
    string msg("Can't create value ");
    msg += i;
    msg += " with sort ";
    msg += sort->to_string();
    throw IncorrectUsageException(msg);
  }
}

Term MsatSolver::make_value(const std::string val,
                            const Sort & sort,
                            unsigned int base) const
{
  SortKind sk = sort->get_sort_kind();
  if (sk == BV)
  {
    return Term(new MsatTerm(
        env, msat_make_bv_number(env, val.c_str(), sort->get_width(), base)));
  }
  else if (sk == REAL || sk == INT)
  {
    // TODO: could use gmp because mathsat needs it anyway
    //       I ran into a nasty bug using the C version of GMP with mathsat
    //       before though and never figured it out (almost seemed like a
    //       compiler bug it was so bizarre)
    if (base != 10)
    {
      throw NotImplementedException(
          "MathSAT only supports base 10 for real and integer values");
    }

    return Term(new MsatTerm(env, msat_make_number(env, val.c_str())));
  }
  else
  {
    string msg("Can't create value ");
    msg += val;
    msg += " with sort ";
    msg += sort->to_string();
    throw IncorrectUsageException(msg);
  }
}

Term MsatSolver::make_value(const Term & val, const Sort & sort) const
{
  if (sort->get_sort_kind() != ARRAY)
  {
    throw IncorrectUsageException(
        "Expecting to create a const array but got a non array sort");
  }
  shared_ptr<MsatSort> msort = static_pointer_cast<MsatSort>(sort);
  shared_ptr<MsatTerm> mval = static_pointer_cast<MsatTerm>(val);
  return Term(
      new MsatTerm(env, msat_make_array_const(env, msort->type, mval->term)));
}

Term MsatSolver::make_term(const string s, const Sort & sort)
{
  if (has_symbol(s))
  {
    string msg("Symbol ");
    msg += s;
    msg += " already exists.";
    throw IncorrectUsageException(msg);
  }

  shared_ptr<MsatSort> msort = static_pointer_cast<MsatSort>(sort);
  msat_decl decl = msat_declare_function(env, s.c_str(), msort->type);

  if (sort->get_sort_kind() == FUNCTION)
  {
    return Term(new MsatTerm(env, decl));
  }
  else
  {
    msat_term res = msat_make_constant(env, decl);
    if (MSAT_ERROR_TERM(res))
    {
      throw InternalSolverException("Got error term.");
    }
    return Term(new MsatTerm(env, res));
  }
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
    for (size_t i = 1; i < op.num_idx; i++)
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
    throw InternalSolverException("Got error term");
  }
  else
  {
    return Term(new MsatTerm(env, res));
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
      res = msat_make_uf(env, mterm0->decl, &v[0]);
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
    throw InternalSolverException("Got error term");
  }
  else
  {
    return Term(new MsatTerm(env, res));
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
      res = msat_make_uf(env, mterm0->decl, &v[0]);
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
    throw InternalSolverException("Got error term");
  }
  else
  {
    return Term(new MsatTerm(env, res));
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
    msat_term res = msat_make_uf(env, uf, &margs[0]);
    if (MSAT_ERROR_TERM(res))
    {
      throw InternalSolverException("Got error term.");
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
  // MathSAT doesn't have a reset that also removes created terms
  // so this does the same thing as reset_assertions
  msat_reset_env(env);
}

void MsatSolver::reset_assertions() { msat_reset_env(env); }

bool MsatSolver::has_symbol(const string name) const
{
  msat_decl decl = msat_find_decl(env, name.c_str());
  if (MSAT_ERROR_DECL(decl))
  {
    return false;
  }
  else
  {
    return true;
  }
}

Term MsatSolver::lookup_symbol(const string name) const
{
  msat_decl decl = msat_find_decl(env, name.c_str());
  if (MSAT_ERROR_DECL(decl))
  {
    string msg("Symbol ");
    msg += name;
    msg += " does not exist.";
    throw IncorrectUsageException(msg);
  }

  // Creating a new constant with the same decl returns
  // the same term in mathsat (e.g. constants are cached)
  return Term(new MsatTerm(env, msat_make_constant(env, decl)));
}

void MsatSolver::dump_smt2(FILE * file) const
{
  throw NotImplementedException("Can't dump all assertions to a file yet");
}

// end MsatSolver implementation

}  // namespace smt
