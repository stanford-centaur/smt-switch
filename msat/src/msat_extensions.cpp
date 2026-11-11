/*********************                                                        */
/*! \file msat_extensions.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Helper functions for certain operations in MathSAT C API
**
**
**/

#ifndef SMT_MSAT_EXTENSIONS_H
#define SMT_MSAT_EXTENSIONS_H

#include "msat_extensions.h"

#include <gmp.h>
#include <mathsat.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "exceptions.h"

using namespace std;

namespace smt {

void detail::MsatFreeDeleter::operator()(void * p) const { msat_free(p); }

string detail::get_msat_string(char * s)
{
  unique_ptr<char, MsatFreeDeleter> owned(s);
  if (!owned)
  {
    throw InternalSolverException("MathSAT failed to print a term or sort");
  }
  return owned.get();
}
msat_term ext_msat_make_negate(msat_env e, msat_term t)
{
  msat_term negone = msat_make_number(e, "-1");
  return msat_make_times(e, negone, t);
}

msat_term ext_msat_make_abs(msat_env e, msat_term t)
{
  msat_term negone = msat_make_number(e, "-1");
  msat_term neg = msat_make_leq(e, t, negone);
  return msat_make_term_ite(e, neg, ext_msat_make_negate(e, t), t);
}

msat_term ext_msat_make_intdiv(msat_env e, msat_term t1, msat_term t2)
{
  // SMT-LIB's div rounds t1 / t2 down for a positive t2 and up for a negative
  // one, so that the remainder is never negative. MathSAT only has floor, and
  // ceil(u) = -floor(-u), whereas floor(u) + 1 is one too large for an
  // integer u.
  msat_term res;
  msat_term div = msat_make_divide(e, t1, t2);
  msat_term div_floor = msat_make_floor(e, div);
  msat_term div_ceil =
      ext_msat_make_negate(e, msat_make_floor(e, ext_msat_make_negate(e, div)));

  if (msat_term_is_number(e, t2))
  {
    mpq_t mval;
    mpq_init(mval);
    msat_term_to_number(e, t2, mval);
    res = (mpq_sgn(mval) >= 0) ? div_floor : div_ceil;
    mpq_clear(mval);
  }
  else
  {
    msat_term zero = msat_make_number(e, "0");
    res =
        msat_make_term_ite(e, msat_make_leq(e, zero, t2), div_floor, div_ceil);
  }

  return res;
}

msat_term ext_msat_make_divisible(msat_env e, std::uint64_t n, msat_term t)
{
  mpz_t modulus;
  mpz_init_set_str(modulus, std::to_string(n).c_str(), 10);
  msat_term res =
      msat_make_int_modular_congruence(e, modulus, t, msat_make_number(e, "0"));
  mpz_clear(modulus);
  return res;
}

msat_term ext_msat_make_nop(msat_env /* e */, msat_term t) { return t; }

msat_term ext_msat_is_int(msat_env e, msat_term t)
{
  return msat_make_eq(e, t, msat_make_floor(e, t));
}

msat_term ext_msat_make_xor(msat_env e, msat_term t0, msat_term t1)
{
  msat_term tor = msat_make_or(e, t0, t1);
  msat_term notboth = msat_make_not(e, msat_make_and(e, t0, t1));
  return msat_make_and(e, tor, notboth);
}

msat_term ext_msat_make_implies(msat_env e, msat_term t0, msat_term t1)
{
  msat_term antecedent = msat_make_not(e, t0);
  return msat_make_or(e, antecedent, t1);
}

msat_term ext_msat_make_ite(msat_env e, msat_term i, msat_term t, msat_term el)
{
  msat_type itype = msat_term_get_type(i);
  msat_type ttype = msat_term_get_type(t);
  msat_type eltype = msat_term_get_type(el);

  if (!msat_is_bool_type(e, itype))
  {
    string msg("Expecting a Boolean condition for ITE but got ");
    throw IncorrectUsageException(
        msg + detail::get_msat_string(msat_to_smtlib2_term(e, i)));
  }

  // msat_make_term_ite takes no Bool branches
  if (msat_is_bool_type(e, ttype) && msat_is_bool_type(e, eltype))
  {
    return msat_make_or(
        e, msat_make_and(e, i, t), msat_make_and(e, msat_make_not(e, i), el));
  }

  // MathSAT makes an integer-valued Real an Int, and accepts an Int branch
  // next to a Real one, so it is left to judge which branches match
  msat_term res = msat_make_term_ite(e, i, t, el);
  if (MSAT_ERROR_TERM(res))
  {
    string msg("Expecting ITE branches of matching sorts but got ");
    msg += detail::get_msat_string(msat_type_repr(ttype));
    msg += " and ";
    msg += detail::get_msat_string(msat_type_repr(eltype));
    throw IncorrectUsageException(msg);
  }
  return res;
}

msat_term ext_msat_make_distinct(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_not(e, msat_make_eq(e, t0, t1));
}

msat_term ext_msat_make_minus(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_plus(e, t0, ext_msat_make_negate(e, t1));
}

msat_term ext_msat_make_lt(msat_env e, msat_term t0, msat_term t1)
{
  // t0 < t1 === !(t1 <= t0)
  return msat_make_not(e, msat_make_leq(e, t1, t0));
}

msat_term ext_msat_make_gt(msat_env e, msat_term t0, msat_term t1)
{
  // t0 > t1 === !(t0 <= t1)
  return msat_make_not(e, msat_make_leq(e, t0, t1));
}

msat_term ext_msat_make_geq(msat_env e, msat_term t0, msat_term t1)
{
  // t0 >= t1 === t1 <= t0
  return msat_make_leq(e, t1, t0);
}

msat_term ext_msat_make_mod(msat_env e, msat_term t0, msat_term t1)
{
  msat_term t0_div_t1 = ext_msat_make_intdiv(e, t0, t1);
  return ext_msat_make_minus(e, t0, msat_make_times(e, t1, t0_div_t1));
}

msat_term ext_msat_make_pow(msat_env e, msat_term t0, msat_term t1)
{
  // msat_make_pow gives back the base for an exponent of 0, rather than 1
  if (msat_term_id(t1) == msat_term_id(msat_make_number(e, "0")))
  {
    return msat_make_number(e, "1");
  }
  return msat_make_pow(e, t0, t1);
}

msat_term ext_msat_make_bv_nand(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_bv_not(e, msat_make_bv_and(e, t0, t1));
}

msat_term ext_msat_make_bv_nor(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_bv_not(e, msat_make_bv_or(e, t0, t1));
}

msat_term ext_msat_make_bv_xnor(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_bv_not(e, msat_make_bv_xor(e, t0, t1));
}

msat_term ext_msat_make_bv_smod(msat_env e, msat_term s, msat_term t)
{
  // From cvc5 rewrite rules
  // (bvsmod s t) abbreviates
  //     (let ((?msb_s ((_ extract |m-1| |m-1|) s))
  //           (?msb_t ((_ extract |m-1| |m-1|) t)))
  //       (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
  //             (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
  //         (let ((u (bvurem abs_s abs_t)))
  //           (ite (= u (_ bv0 m))
  //                u
  //           (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
  //                u
  //           (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
  //                (bvadd (bvneg u) t)
  //           (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
  //                (bvadd u t)
  //                (bvneg u))))))))

  size_t width;
  if (!msat_is_bv_type(e, msat_term_get_type(s), &width))
  {
    throw IncorrectUsageException("Expecting a bit-vector type in bvsmod");
  }

  msat_term one_1bit = msat_make_bv_int_number(e, 1, 1);
  msat_term zero_1bit = msat_make_bv_int_number(e, 0, 1);
  msat_term zero_width = msat_make_bv_int_number(e, 0, width);

  msat_term msb_s = msat_make_bv_extract(e, width - 1, width - 1, s);
  msat_term msb_t = msat_make_bv_extract(e, width - 1, width - 1, t);

  msat_term abs_s = msat_make_term_ite(
      e, msat_make_eq(e, msb_s, zero_1bit), s, msat_make_bv_neg(e, s));
  msat_term abs_t = msat_make_term_ite(
      e, msat_make_eq(e, msb_t, zero_1bit), t, msat_make_bv_neg(e, t));

  msat_term u = msat_make_bv_urem(e, abs_s, abs_t);

  msat_term ite_3 =
      msat_make_term_ite(e,
                         msat_make_and(e,
                                       msat_make_eq(e, msb_s, zero_1bit),
                                       msat_make_eq(e, msb_t, one_1bit)),
                         msat_make_bv_plus(e, u, t),
                         msat_make_bv_neg(e, u));
  msat_term ite_2 =
      msat_make_term_ite(e,
                         msat_make_and(e,
                                       msat_make_eq(e, msb_s, one_1bit),
                                       msat_make_eq(e, msb_t, zero_1bit)),
                         msat_make_bv_plus(e, msat_make_bv_neg(e, u), t),
                         ite_3);

  msat_term ite_1 =
      msat_make_term_ite(e,
                         msat_make_and(e,
                                       msat_make_eq(e, msb_s, zero_1bit),
                                       msat_make_eq(e, msb_t, zero_1bit)),
                         u,
                         ite_2);

  msat_term ite_0 =
      msat_make_term_ite(e, msat_make_eq(e, u, zero_width), u, ite_1);

  return ite_0;
}

msat_term ext_msat_make_bv_ugt(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_not(e, msat_make_bv_uleq(e, t0, t1));
}

msat_term ext_msat_make_bv_ugeq(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_not(e, msat_make_bv_ult(e, t0, t1));
}

msat_term ext_msat_make_bv_sgt(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_not(e, msat_make_bv_sleq(e, t0, t1));
}

msat_term ext_msat_make_bv_sgeq(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_not(e, msat_make_bv_slt(e, t0, t1));
}

/**
 * Wraps msat_make_uf and converts boolean arguments to bitvectors of size 1
 * because mathsat doesn't support UF over booleans
 */
msat_term ext_msat_make_uf(msat_env e,
                           msat_decl func,
                           std::vector<msat_term> args)
{
  std::vector<msat_term> converted_args;
  msat_type arg_type;
  for (auto a : args)
  {
    arg_type = msat_term_get_type(a);
    if (msat_is_bool_type(e, arg_type))
    {
      converted_args.push_back(
          msat_make_term_ite(e,
                             a,
                             msat_make_bv_number(e, "1", 1, 2),
                             msat_make_bv_number(e, "0", 1, 2)));
    }
    else
    {
      converted_args.push_back(a);
    }
  }

  msat_term res = msat_make_uf(e, func, converted_args.data());
  if (MSAT_ERROR_TERM(res))
  {
    throw InternalSolverException("Got an error term in function application");
  }
  return res;
}

}  // namespace smt

#endif
