/*********************                                                        */
/*! \file msat_term.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief MathSAT implementation of AbsTerm
**
**
**/

#include "msat_term.h"

#include <cstddef>
#include <cstdint>
#include <functional>
#include <vector>

#include "exceptions.h"
#include "msat_extensions.h"
#include "msat_sort.h"
#include "ops.h"
#include "utils.h"

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
    char * s = msat_to_smtlib2_term(e, t);
    std::string msg("The modulus of the Msat term ");
    msg += s;
    msg += " does not fit in an op index.";
    msat_free(s);
    throw NotImplementedException(msg);
  }
  return res;
}

// MsatTerm implementation

MsatTerm::MsatTerm(const std::shared_ptr<msat_env> & e, msat_term t)
    : env(e), term(t)
{
}

MsatTerm::MsatTerm(const std::shared_ptr<msat_env> & e, msat_decl d)
    : env(e), decl(d), is_uf(true)
{
}

size_t MsatTerm::hash() const
{
  // MathSAT numbers terms per environment, so mix in the environment, as
  // compare checks it
  size_t h = std::hash<msat_env *>{}(env.get());
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
  else if (msat_term_is_forall(*env, term))
  {
    return Op(Forall);
  }
  else if (msat_term_is_exists(*env, term))
  {
    return Op(Exists);
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
      char * s = msat_to_smtlib2_term(*env, term);
      std::string msg("Msat term ");
      msg += s;
      msg += " has an unknown op.";
      msat_free(s);
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
      throw InternalSolverException("Expecting non-zero arity for UF.");
    }

    msat_type funtype = msat_get_function_type(*env,
                                               param_types.data(),
                                               param_types.size(),
                                               msat_decl_get_return_type(decl));

    return std::make_shared<MsatSort>(env, funtype, decl);
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

  // an abstract value, which an uninterpreted sort has, is a constant whose
  // name starts with @, as SMT-LIB reserves for them
  if (!msat_term_is_constant(*env, term))
  {
    return false;
  }
  char * name = msat_decl_get_name(msat_term_get_decl(term));
  bool res = name[0] == '@';
  msat_free(name);
  return res;
}

string MsatTerm::to_string() const
{
  if (is_uf)
  {
    if (MSAT_ERROR_DECL(decl))
    {
      throw SmtException("Can't get representation for MathSAT error decl!");
    }
    string repr = msat_decl_repr(decl);
    size_t idx = repr.find(":");
    if (idx != string::npos)
    {
      repr = repr.substr(0, idx);
    }
    return repr;
  }
  else
  {
    if (MSAT_ERROR_TERM(term))
    {
      throw SmtException("Can't get representation for MathSAT error term!");
    }
    char * s = msat_to_smtlib2_term(*env, term);
    string res = s;
    msat_free(s);
    return res;
  }
}

/** Returns the text of a MathSAT number term, and whether it is a
 *  bit-vector, or throws if the term is not a number.
 *  Bit-vectors are printed in SMT-LIB, as (_ bvN W). Other numbers are
 *  printed as, e.g., -5 or 1/2, because MathSAT's SMT-LIB printer writes
 *  the minimum int64_t as (- -9223372036854775808).
 */
static string number_to_text(msat_env env,
                             msat_term term,
                             bool is_uf,
                             bool & is_bv)
{
  if (is_uf)
  {
    throw IncorrectUsageException(
        "Can't convert a function symbol to an integer");
  }
  is_bv = msat_is_bv_type(env, msat_term_get_type(term), nullptr);
  const bool is_number = msat_term_is_number(env, term);
  char * s = (is_bv || !is_number) ? msat_to_smtlib2_term(env, term)
                                   : msat_term_repr(term);
  string val = s;
  msat_free(s);
  if (!is_number)
  {
    throw IncorrectUsageException("Can't convert " + val
                                  + " to an integer: it is not a number");
  }
  return val;
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
  char * s = msat_decl_get_name(msat_term_get_decl(term));
  // MathSAT names a variable with a quote before the name it was made with
  string res = s + 1;
  msat_free(s);
  return res;
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
  char * s = msat_decl_get_name(is_uf ? decl : msat_term_get_decl(term));
  string res = s;
  msat_free(s);
  return res;
}

uint64_t MsatTerm::to_int() const
{
  bool is_bv;
  const string val = number_to_text(*env, term, is_uf, is_bv);
  return is_bv ? smtlib_bv_to_uint64(val) : smtlib_int_to_uint64(val);
}

int64_t MsatTerm::to_signed_int() const
{
  bool is_bv;
  const string val = number_to_text(*env, term, is_uf, is_bv);
  return is_bv ? smtlib_bv_to_int64(val) : smtlib_int_to_int64(val);
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
        "Cannot use print_value_as on a non-value term.");
  }
  return to_string();
}

msat_term MsatTerm::get_msat_term() const
{
  if (is_uf)
  {
    throw IncorrectUsageException("Cannot get msat_term from UF.");
  }
  return term;
}

msat_decl MsatTerm::get_msat_decl() const
{
  if (!is_uf)
  {
    throw IncorrectUsageException("Cannot get msat_decl from term.");
  }
  return decl;
}

// end MsatTerm implementation

}  // namespace smt
