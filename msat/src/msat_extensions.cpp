#ifndef SMT_MSAT_EXTENSIONS_H
#define SMT_MSAT_EXTENSIONS_H

#include "mathsat.h"

#include "exceptions.h"

using namespace std;

namespace smt {
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
  msat_term res;
  msat_term div = msat_make_divide(e, t1, t2);
  msat_term div_floor = msat_make_floor(e, div);
  msat_term div_ceil = msat_make_plus(e, div_floor, msat_make_number(e, "1"));

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
    msat_term t2_pos = msat_make_leq(e, t2, zero);
    res = msat_make_term_ite(e, t2_pos, div_floor, div_ceil);
  }

  return res;
}

msat_term ext_msat_make_nop(msat_env e, msat_term t) { return t; }

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
    string msg("Expecting a boolean term for first ITE argument but got\n\t");
    throw IncorrectUsageException(msg + msat_to_smtlib2_term(e, i));
  }

  if (!msat_type_equals(ttype, eltype))
  {
    string msg("Expecting matching branch terms for ITE but got\n\t");
    throw IncorrectUsageException(msg + msat_type_repr(ttype) + " "
                                  + msat_type_repr(eltype));
  }

  if (msat_is_bool_type(e, ttype))
  {
    return msat_make_or(
        e, msat_make_and(e, i, t), msat_make_and(e, msat_make_not(e, i), el));
  }
  else
  {
    return msat_make_term_ite(e, i, t, el);
  }
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
  throw NotImplementedException("mod not implemented.");
}

msat_term ext_msat_make_pow(msat_env e, msat_term t0, msat_term t1)
{
  throw NotImplementedException("pow not implemented");
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
  // From CVC4 rewrite rules
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

msat_term ext_msat_make_bv_number(msat_env e,
                                  const char * val,
                                  size_t size,
                                  int base)
{
  // gmp should be included because it's a dependency of mathsat
  mpz_t mval;
  mpz_init(mval);
  int status = mpz_set_str(mval, val, base);

  if (status != 0)
  {
    std::string msg("Could not create bv from ");
    msg += val;
    throw IncorrectUsageException(msg);
  }

  msat_term res;

  // mpz_t values for bounds checking
  mpz_t exclusive_upper_bnd;
  mpz_init(exclusive_upper_bnd);
  mpz_ui_pow_ui(exclusive_upper_bnd, 2, size);

  if (mpz_sgn(mval) < 0)
  {
    // for overflow checking
    mpz_t tmp;
    mpz_init(tmp);
    mpz_t lower_bnd;
    mpz_init(lower_bnd);

    mpz_ui_pow_ui(tmp, 2, size - 1);
    mpz_neg(lower_bnd, tmp);

    if (mpz_cmp(mval, lower_bnd) < 0)
    {
      std::string msg("Can't represent ");
      msg += val;
      msg += " in " + std::to_string(size) + " bits.";
      mpz_clear(lower_bnd);
      mpz_clear(tmp);
      mpz_clear(exclusive_upper_bnd);
      mpz_clear(mval);
      throw IncorrectUsageException(msg);
    }

    mpz_t negval;
    mpz_init(negval);
    mpz_neg(negval, mval);
    res = msat_make_bv_mpz_number(e, negval, size);
    if (MSAT_ERROR_TERM(res))
    {
      std::string msg("Error creating bit-vector from ");
      msg += val;
      mpz_clear(negval);
      mpz_clear(lower_bnd);
      mpz_clear(tmp);
      mpz_clear(exclusive_upper_bnd);
      mpz_clear(mval);
      throw IncorrectUsageException(msg);
    }
    res = msat_make_bv_neg(e, res);
    mpz_clear(negval);
    mpz_clear(lower_bnd);
    mpz_clear(tmp);
  }
  else
  {
    if (mpz_cmp(mval, exclusive_upper_bnd) >= 0)
    {
      std::string msg("Can't represent ");
      msg += val;
      msg += " in " + std::to_string(size) + " bits.";
      mpz_clear(exclusive_upper_bnd);
      mpz_clear(mval);
      throw IncorrectUsageException(msg);
    }
    res = msat_make_bv_mpz_number(e, mval, size);
  }

  mpz_clear(exclusive_upper_bnd);
  mpz_clear(mval);

  if (MSAT_ERROR_TERM(res))
  {
    std::string msg("Error creating bit-vector from ");
    msg += val;
    throw IncorrectUsageException(msg);
  }

  return res;
}

}  // namespace smt

#endif
