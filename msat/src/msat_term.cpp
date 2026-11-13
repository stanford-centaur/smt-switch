/*!
 * \file msat_term.cpp
 * \brief MathSAT implementation of AbsTerm
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/msat_term.h"

#include <gmp.h>

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/msat_extensions.h"
#include "smt-switch/msat_sort.h"
#include "smt-switch/ops.h"
#include "smt-switch/utils.h"

using namespace std;

namespace smt {

// MathSAT's congruence t1 = t2 mod n, i.e. n divides t1 - t2, is smt-switch's
// (_ divisible n) with the one child t1 - t2. t2 can't be dropped: MathSAT
// moves the constant part into t2, e.g. x + 1 = 0 mod 3 is stored as
// x = -1 mod 3.
static bool is_congruence(msat_env e, msat_term t)
{
  return msat_decl_get_tag(e, msat_term_get_decl(t)) == MSAT_TAG_INT_MOD_CONGR;
}

/** The modulus n of a congruence t1 = t2 mod n
 *  @throws NotImplementedException if n does not fit in an op index
 */
static uint64_t congruence_modulus(msat_env e, msat_term t)
{
  mpz_t modulus;
  mpz_init(modulus);
  if (!msat_term_is_int_modular_congruence(e, t, modulus))
  {
    mpz_clear(modulus);
    throw InternalSolverException(
        "MathSAT tagged a term as a congruence but gave no modulus for it");
  }
  bool fits = mpz_fits_ulong_p(modulus);
  uint64_t res = fits ? mpz_get_ui(modulus) : 0;
  mpz_clear(modulus);
  if (!fits)
  {
    std::string msg("The modulus of the MathSAT term ");
    msg += detail::get_msat_string(msat_to_smtlib2_term(e, t));
    msg += " does not fit in an op index";
    throw NotImplementedException(msg);
  }
  return res;
}

// MsatTerm implementation

MsatTerm::MsatTerm(const std::shared_ptr<MsatEnv> & e, msat_term t)
    : env(e), term(t)
{
}

MsatTerm::MsatTerm(const std::shared_ptr<MsatEnv> & e, msat_decl d)
    : env(e), decl(d), is_uf(true)
{
}

size_t MsatTerm::hash() const
{
  // MathSAT numbers terms per environment, so mix in the environment, as
  // compare checks it
  size_t h = std::hash<MsatEnv *>{}(env.get());
  detail::hash_combine(h, get_id());
  return h;
}

size_t MsatTerm::get_id() const
{
  if (!is_uf)
  {
    return msat_term_id(term);
  }
  else
  {
    return msat_decl_id(decl);
  }
}

bool MsatTerm::compare(const Term & absterm) const
{
  shared_ptr<MsatTerm> mterm = std::dynamic_pointer_cast<MsatTerm>(absterm);
  if (!mterm || env != mterm->env)
  {
    // ids are unique only within one environment
    return false;
  }
  if (is_uf ^ mterm->is_uf)
  {
    // can't be equal if one is a uf and the other is not
    return false;
  }
  else if (!is_uf)
  {
    return (msat_term_id(term) == msat_term_id(mterm->term));
  }
  else
  {
    return (msat_decl_id(decl) == msat_decl_id(mterm->decl));
  }
}

Op MsatTerm::get_op() const
{
  if (is_uf)
  {
    // uninterpreted function has no op
    return Op();
  }
  else if (msat_term_is_and(*env, term))
  {
    return Op(And);
  }
  else if (msat_term_is_or(*env, term))
  {
    return Op(Or);
  }
  else if (msat_term_is_not(*env, term))
  {
    return Op(Not);
  }
  else if (msat_term_is_iff(*env, term))
  {
    return Op(Equal);
  }
  else if (msat_term_is_term_ite(*env, term))
  {
    return Op(Ite);
  }
  else if (msat_term_is_constant(*env, term))
  {
    return Op();
  }
  else if (msat_term_is_uf(*env, term))
  {
    return Op(Apply);
  }
  else if (msat_term_is_equal(*env, term))
  {
    return Op(Equal);
  }
  else if (msat_term_is_leq(*env, term))
  {
    return Op(Le);
  }
  else if (msat_term_is_plus(*env, term))
  {
    return Op(Plus);
  }
  else if (msat_term_is_times(*env, term))
  {
    return Op(Mult);
  }
  else if (msat_term_is_divide(*env, term))
  {
    return Op(Div);
  }
  else if (msat_term_is_array_read(*env, term))
  {
    return Op(Select);
  }
  else if (msat_term_is_array_write(*env, term))
  {
    return Op(Store);
  }
  else if (msat_term_is_array_const(*env, term))
  {
    // constant array is a value (has a null operator)
    return Op();
  }
  else if (msat_term_is_bv_concat(*env, term))
  {
    return Op(Concat);
  }
  else if (msat_term_is_bv_or(*env, term))
  {
    return Op(BVOr);
  }
  else if (msat_term_is_bv_xor(*env, term))
  {
    return Op(BVXor);
  }
  else if (msat_term_is_bv_and(*env, term))
  {
    return Op(BVAnd);
  }
  else if (msat_term_is_bv_not(*env, term))
  {
    return Op(BVNot);
  }
  else if (msat_term_is_bv_plus(*env, term))
  {
    return Op(BVAdd);
  }
  else if (msat_term_is_bv_minus(*env, term))
  {
    return Op(BVSub);
  }
  else if (msat_term_is_bv_times(*env, term))
  {
    return Op(BVMul);
  }
  else if (msat_term_is_bv_neg(*env, term))
  {
    return Op(BVNeg);
  }
  else if (msat_term_is_bv_udiv(*env, term))
  {
    return Op(BVUdiv);
  }
  else if (msat_term_is_bv_urem(*env, term))
  {
    return Op(BVUrem);
  }
  else if (msat_term_is_bv_sdiv(*env, term))
  {
    return Op(BVSdiv);
  }
  else if (msat_term_is_bv_srem(*env, term))
  {
    return Op(BVSrem);
  }
  else if (msat_term_is_bv_ult(*env, term))
  {
    return Op(BVUlt);
  }
  else if (msat_term_is_bv_uleq(*env, term))
  {
    return Op(BVUle);
  }
  else if (msat_term_is_bv_slt(*env, term))
  {
    return Op(BVSlt);
  }
  else if (msat_term_is_bv_sleq(*env, term))
  {
    return Op(BVSle);
  }
  else if (msat_term_is_bv_lshl(*env, term))
  {
    return Op(BVShl);
  }
  else if (msat_term_is_bv_lshr(*env, term))
  {
    return Op(BVLshr);
  }
  else if (msat_term_is_bv_ashr(*env, term))
  {
    return Op(BVAshr);
  }
  else if (msat_term_is_bv_comp(*env, term))
  {
    return Op(BVComp);
  }
  else if (is_symbol() || is_value())
  {
    return Op();
  }
  else if (msat_term_is_floor(*env, term))
  {
    return Op(To_Int);
  }
  else if (is_congruence(*env, term))
  {
    return Op(Divisible, congruence_modulus(*env, term));
  }
  else if (msat_term_is_int_from_ubv(*env, term))
  {
    return Op(UBV_To_Int);
  }
  else if (msat_term_is_int_from_sbv(*env, term))
  {
    return Op(SBV_To_Int);
  }
  else if (msat_term_is_int_to_bv(*env, term))
  {
    return Op(Int_To_BV, get_sort()->get_width());
  }
  else
  {
    size_t idx0;
    size_t idx1;
    if (msat_term_is_bv_extract(*env, term, &idx0, &idx1))
    {
      return Op(Extract, idx0, idx1);
    }
    else if (msat_term_is_bv_zext(*env, term, &idx0))
    {
      return Op(Zero_Extend, idx0);
    }
    else if (msat_term_is_bv_sext(*env, term, &idx0))
    {
      return Op(Sign_Extend, idx0);
    }
    else if (msat_term_is_bv_rol(*env, term, &idx0))
    {
      return Op(Rotate_Left, idx0);
    }
    else if (msat_term_is_bv_ror(*env, term, &idx0))
    {
      return Op(Rotate_Right, idx0);
    }
    else
    {
      std::string msg("smt-switch has no PrimOp for the MathSAT term ");
      msg += detail::get_msat_string(msat_to_smtlib2_term(*env, term));
      throw NotImplementedException(msg);
    }
  }
}

Sort MsatTerm::get_sort() const
{
  if (!is_uf)
  {
    return std::make_shared<MsatSort>(env, msat_term_get_type(term));
  }
  else
  {
    // need to reconstruct the function type
    vector<msat_type> param_types;
    size_t arity = msat_decl_get_arity(decl);
    param_types.reserve(arity);
    for (size_t i = 0; i < arity; i++)
    {
      param_types.push_back(msat_decl_get_arg_type(decl, i));
    }

    if (!param_types.size())
    {
      throw InternalSolverException(
          "Expecting a nonzero arity for an uninterpreted function");
    }

    msat_type funtype = msat_get_function_type(*env,
                                               param_types.data(),
                                               param_types.size(),
                                               msat_decl_get_return_type(decl));

    return std::make_shared<MsatSort>(env, funtype);
  }
}

bool MsatTerm::is_symbol() const
{
  // functions are currently considered symbols
  if (is_uf)
  {
    return true;
  }

  // a symbolic constant is a term with no children and no built-in
  // interpretation
  return (
      (msat_term_arity(term) == 0)
      && (msat_decl_get_tag(*env, msat_term_get_decl(term)) == MSAT_TAG_UNKNOWN)
      && !is_value());
}

bool MsatTerm::is_param() const
{
  // a function term holds only its declaration, not a term to ask about
  return !is_uf && msat_term_is_variable(*env, term);
}

bool MsatTerm::is_symbolic_const() const
{
  // functions and parameters are not constants
  if (is_uf || is_param())
  {
    return false;
  }

  return is_symbol();
}

bool MsatTerm::is_value() const
{
  if (is_uf)
  {
    return false;
  }

  if (msat_term_is_number(*env, term) || msat_term_is_true(*env, term)
      || msat_term_is_false(*env, term) || msat_term_is_array_const(*env, term))
  {
    return true;
  }

  if (msat_term_is_array_write(*env, term))
  {
    // SMT-LIB's ArraysEx makes a store of a value into an array value a value
    for (const Term & c : *this)
    {
      if (!c->is_value())
      {
        return false;
      }
    }
    return true;
  }

  // an abstract value, which an uninterpreted sort has, is a constant whose
  // name starts with @, as SMT-LIB reserves for them
  if (!msat_term_is_constant(*env, term))
  {
    return false;
  }
  string name =
      detail::get_msat_string(msat_decl_get_name(msat_term_get_decl(term)));
  return name[0] == '@';
}

string MsatTerm::to_string() const
{
  if (is_uf)
  {
    if (MSAT_ERROR_DECL(decl))
    {
      throw SmtException("Can't print a MathSAT error declaration");
    }
    return smtlib_quote_symbol(get_symbol_name());
  }
  else
  {
    if (MSAT_ERROR_TERM(term))
    {
      throw SmtException("Can't print a MathSAT error term");
    }
    return detail::get_msat_string(msat_to_smtlib2_term(*env, term));
  }
}

/** Returns the text of a MathSAT arithmetic number term, or throws if the
 *  term is not a number.
 *  Numbers are printed as, e.g., -5 or 1/2, because MathSAT's SMT-LIB
 *  printer writes the minimum int64_t as (- -9223372036854775808).
 */
static string number_to_text(msat_env env, msat_term term, bool is_uf)
{
  if (is_uf)
  {
    throw IncorrectUsageException(
        "Can't convert a function symbol to an integer");
  }
  if (!msat_term_is_number(env, term))
  {
    throw IncorrectUsageException(
        "Can't convert "
        + detail::get_msat_string(msat_to_smtlib2_term(env, term))
        + " to an integer: it is not a number");
  }
  return detail::get_msat_string(msat_term_repr(term));
}

string MsatTerm::get_constructor_name() const
{
  throw IncorrectUsageException(
      "Only a constructor or a tester has a constructor name");
}

string MsatTerm::get_param_name() const
{
  if (!is_param())
  {
    throw IncorrectUsageException("Only a param has a param name");
  }
  // MathSAT names a variable with a quote before the name it was made with
  return detail::get_msat_string(msat_decl_get_name(msat_term_get_decl(term)))
      .substr(1);
}

string MsatTerm::get_selector_name() const
{
  throw IncorrectUsageException("Only a selector has a selector name");
}

string MsatTerm::get_symbol_name() const
{
  // A function has a declaration but no term, which is_param would read.
  if (!is_uf && (!is_symbol() || is_param()))
  {
    throw IncorrectUsageException(
        "Only a symbol that is not a param has a symbol name");
  }
  return detail::get_msat_string(
      msat_decl_get_name(is_uf ? decl : msat_term_get_decl(term)));
}

uint64_t MsatTerm::to_int() const
{
  if (!is_uf && msat_is_bv_type(*env, msat_term_get_type(term), nullptr))
  {
    return bits_to_uint64(to_bits());
  }
  return smtlib_int_to_uint64(number_to_text(*env, term, is_uf));
}

int64_t MsatTerm::to_signed_int() const
{
  if (!is_uf && msat_is_bv_type(*env, msat_term_get_type(term), nullptr))
  {
    return bits_to_int64(to_bits());
  }
  return smtlib_int_to_int64(number_to_text(*env, term, is_uf));
}

string MsatTerm::to_bits() const
{
  size_t width = 0;
  if (is_uf || !msat_is_bv_type(*env, msat_term_get_type(term), &width)
      || !msat_term_is_number(*env, term))
  {
    throw IncorrectUsageException(
        "Can't get a bitstring from a term that is not a bit-vector value");
  }
  mpq_t value;
  mpq_init(value);
  msat_term_to_number(*env, term, value);
  string bits(width, '0');
  for (size_t i = 0; i < width; ++i)
  {
    if (mpz_tstbit(mpq_numref(value), i))
    {
      bits[width - 1 - i] = '1';
    }
  }
  mpq_clear(value);
  return bits;
}

bool MsatTerm::to_bool() const
{
  if (!is_uf)
  {
    if (msat_term_is_true(*env, term))
    {
      return true;
    }
    if (msat_term_is_false(*env, term))
    {
      return false;
    }
  }
  throw IncorrectUsageException("Can't convert " + to_string()
                                + " to a Boolean: it is not a Boolean value");
}

// The children smt-switch lists, with the function first in an application.
// A function symbol has no term, and so no children.
std::size_t MsatTerm::get_num_children() const
{
  if (MSAT_ERROR_TERM(term))
  {
    return 0;
  }
  if (is_congruence(*env, term))
  {
    // the one child t1 - t2
    return 1;
  }
  std::size_t arity = msat_term_arity(term);
  return msat_term_is_uf(*env, term) ? arity + 1 : arity;
}

Term MsatTerm::get_child(std::size_t i) const
{
  if (is_congruence(*env, term))
  {
    return std::make_shared<MsatTerm>(
        env,
        ext_msat_make_minus(
            *env, msat_term_get_arg(term, 0), msat_term_get_arg(term, 1)));
  }
  else if (!i && msat_term_is_uf(*env, term))
  {
    return std::make_shared<MsatTerm>(env, msat_term_get_decl(term));
  }
  else
  {
    std::size_t actual_idx = i;
    if (msat_term_is_uf(*env, term))
    {
      actual_idx--;
    }

    return std::make_shared<MsatTerm>(env, msat_term_get_arg(term, actual_idx));
  }
}

std::string MsatTerm::print_value_as(SortKind /* sk */) const
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Can't use print_value_as on a term that is not a value");
  }
  return to_string();
}

msat_term MsatTerm::get_msat_term() const
{
  if (is_uf)
  {
    throw IncorrectUsageException("Can't get the msat_term of a function");
  }
  return term;
}

msat_decl MsatTerm::get_msat_decl() const
{
  if (!is_uf)
  {
    throw IncorrectUsageException(
        "Can't get the msat_decl of a term that is not a function");
  }
  return decl;
}

// end MsatTerm implementation

}  // namespace smt
