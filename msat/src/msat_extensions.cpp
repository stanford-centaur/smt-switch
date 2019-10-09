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
  return msat_make_bv_not(e, msat_make_and(e, t0, t1));
}

msat_term ext_msat_make_bv_nor(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_bv_not(e, msat_make_or(e, t0, t1));
}

msat_term ext_msat_make_bv_xnor(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_bv_not(e, ext_msat_make_xor(e, t0, t1));
}

msat_term ext_msat_make_bv_smod(msat_env e, msat_term t0, msat_term t1)
{
  throw NotImplementedException("smod not implemented");
}

msat_term ext_msat_make_bv_ugt(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_bv_not(e, msat_make_bv_uleq(e, t0, t1));
}

msat_term ext_msat_make_bv_ugeq(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_bv_not(e, msat_make_bv_ult(e, t0, t1));
}

msat_term ext_msat_make_bv_sgt(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_bv_not(e, msat_make_bv_sleq(e, t0, t1));
}

msat_term ext_msat_make_bv_sgeq(msat_env e, msat_term t0, msat_term t1)
{
  return msat_make_bv_not(e, msat_make_bv_slt(e, t0, t1));
}

}  // namespace smt

#endif
